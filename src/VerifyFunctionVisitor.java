import com.sun.source.tree.MethodTree;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Position;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTreeUtils;

import javax.lang.model.element.Modifier;
import java.util.LinkedHashMap;

import static com.sun.tools.javac.tree.JCTree.*;
import static org.jmlspecs.openjml.JmlTree.*;

/**
 * Created by jklamroth on 11/13/18.
 *
 * This Visitor translates methods and their translation into Java!?
 */
public class VerifyFunctionVisitor extends FilterVisitor {
    private final Maker M;
    private final Context context;
    private final Symtab syms;
    private final JmlTreeUtils treeutils;
    private final ClassReader reader;
    protected JmlMethodDecl currentMethod;
    private List<JCStatement> newStatements = List.nil();
    private List<JCStatement> combinedNewReqStatements = List.nil();
    private List<JCStatement> combinedNewEnsStatements = List.nil();
    private List<List<JCStatement>> reqCases = List.nil();
    private List<List<JCStatement>> ensCases = List.nil();
    private Symbol returnVar = null;
    private boolean hasReturn = false;
    private VerifyFunctionVisitor.TranslationMode translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
    //Has to perserve order (e.g. LinkedHashMap)
    private LinkedHashMap<JCExpression, JCVariableDecl> oldVars = new LinkedHashMap<>();
    private List<JCStatement> oldInits = List.nil();
    private  final BaseVisitor baseVisitor;
    private List<JCExpression> currentAssignable = null;

    public enum TranslationMode {ASSUME, ASSERT, JAVA, DEMONIC}

    public VerifyFunctionVisitor(Context context, Maker maker, BaseVisitor base) {
        super(context, maker);
        baseVisitor = base;
        this.context = context;
        this.M = Maker.instance(context);
        this.syms = Symtab.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlMethodClauseExpr that, Void p) {
        //JmlMethodClauseExpr copy = (JmlMethodClauseExpr)super.visitJmlMethodClauseExpr(that, p);
        JmlExpressionVisitor expressionVisitor = new JmlExpressionVisitor(context, M, baseVisitor, translationMode, oldVars, returnVar, currentMethod);

        if(that.clauseKind.name().equals("ensures")) {
            expressionVisitor.setTranslationMode(TranslationMode.ASSERT);
            translationMode = TranslationMode.ASSERT;
        } else if(that.clauseKind.name().equals("requires")) {
            expressionVisitor.setTranslationMode(TranslationMode.ASSUME);
            translationMode = TranslationMode.ASSUME;
        }
        JCExpression normalized = NormalizeVisitor.normalize(that.expression, context, M);
        JCExpression copy = expressionVisitor.copy(normalized);
        newStatements = expressionVisitor.getNewStatements();
        oldVars.putAll(expressionVisitor.getOldVars());
        oldInits = oldInits.appendList(expressionVisitor.getOldInits());
        newStatements = newStatements.prependList(expressionVisitor.getNeededVariableDefs());
        newStatements = newStatements.append(TranslationUtils.makeAssumeOrAssertStatement(copy, translationMode));
        if(translationMode == TranslationMode.ASSERT) {
            combinedNewEnsStatements = combinedNewEnsStatements.append(M.Block(0L, newStatements));
        } else if(translationMode == TranslationMode.ASSUME) {
            combinedNewReqStatements = combinedNewReqStatements.append(M.Block(0L, newStatements));
        }
        newStatements = List.nil();
        translationMode = VerifyFunctionVisitor.TranslationMode.JAVA;
        return M.JmlMethodClauseExpr(that.clauseKind.name(), that.clauseKind, copy);
    }

    @Override
    public JCTree visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that, Void p) {
        if(currentAssignable == null) {
            currentAssignable = List.nil();
        }
        if(that.list != null) {
            if(that.list.stream().anyMatch(loc -> loc instanceof JmlStoreRefKeyword
            && ((JmlStoreRefKeyword) loc).token.equals(JmlTokenKind.BSNOTHING))) {
                if(that.list.size() + currentAssignable.size() > 1) {
                    throw new RuntimeException("Assignable containing \\nothing and something else is not valid.");
                }
            } else {
                currentAssignable = currentAssignable.appendList(that.list);
            }
        }
        return super.visitJmlMethodClauseStoreRef(that, p);
    }

    @Override
    public JCTree visitJmlStatementSpec(JmlStatementSpec that, Void p) {
        return that;
    }

    @Override
    public JCTree visitJmlSpecificationCase(JmlSpecificationCase that, Void p) {
        combinedNewEnsStatements = List.nil();
        combinedNewReqStatements = List.nil();
        JCTree copy = super.visitJmlSpecificationCase(that, p);
        ensCases = ensCases.append(combinedNewEnsStatements);
        reqCases = reqCases.append(combinedNewReqStatements);
        combinedNewEnsStatements = List.nil();
        combinedNewReqStatements = List.nil();
        return copy;
    }

    @Override
    public JCTree visitJmlMethodDecl(JmlMethodDecl that, Void p) {
        currentAssignable = null;
        currentMethod = (JmlMethodDecl)that.clone();
        if(currentMethod.mods.getFlags().contains(Modifier.ABSTRACT)) {
            return currentMethod;
        }
        hasReturn = false;
        oldVars = new LinkedHashMap<>();
        oldInits = List.nil();
        JCVariableDecl returnVar = null;
        Type t = that.sym.getReturnType();
        if(!(t instanceof Type.JCVoidType)) {
            returnVar = treeutils.makeVarDef(t, M.Name("returnVar"), currentMethod.sym, getLiteralForType(t));
            hasReturn = true;
            this.returnVar = returnVar.sym;
        } else {
            this.returnVar = null;
        }
        JCVariableDecl specCaseID = TranslationUtils.makeNondetIntVar(M.Name("specCaseId"), currentMethod.sym);
        JmlMethodDecl copy = (JmlMethodDecl)visitJmlMethodDeclBugfix(that, p);
        JCVariableDecl catchVar = treeutils.makeVarDef(syms.exceptionType, M.Name("e"), currentMethod.sym, Position.NOPOS);
        JCExpression ty = M.at(that).Type(syms.runtimeExceptionType);
        JCExpression msg = treeutils.makeStringLiteral(that.pos, "Specification is not well defined for method " + that.getName());
        JCThrow throwStmt = M.Throw(M.NewClass(null, null, ty, List.of(msg), null));
//        JCTry reqTry = M.Try(M.Block(0L, List.from(combinedNewReqStatements)),
//                List.of(M.Catch(catchVar, M.Block(0L, List.of(throwStmt)))), null);
//        JCTry ensTry = M.Try(M.Block(0L, List.from(combinedNewEnsStatements)),
//                List.of(M.Catch(catchVar, M.Block(0L, List.of(throwStmt)))), null);

        JCVariableDecl catchVarb = treeutils.makeVarDef(baseVisitor.getExceptionClass().type, M.Name("ex"), currentMethod.sym, Position.NOPOS);

        List<JCStatement> invariantAssert = List.nil();
        for(JCExpression expression : baseVisitor.getInvariants()) {
            expression = NormalizeVisitor.normalize(expression, context, M);
            JmlExpressionVisitor ev = new JmlExpressionVisitor(context, M, baseVisitor, TranslationMode.ASSERT, oldVars, this.returnVar, currentMethod);
            JCExpression invCopy = ev.copy(expression);
            oldVars.putAll(ev.getOldVars());
            oldInits = oldInits.appendList(ev.getOldInits());
            invariantAssert = invariantAssert.prependList(ev.getNeededVariableDefs());
            invariantAssert = invariantAssert.appendList(ev.getNewStatements());
            invariantAssert = invariantAssert.append(TranslationUtils.makeAssumeOrAssertStatement(invCopy, TranslationMode.ASSERT));
        }
        List<JCStatement> invariantAssume = List.nil();
        for(JCExpression expression : baseVisitor.getInvariants()) {
            expression = NormalizeVisitor.normalize(expression, context, M);
            JmlExpressionVisitor ev = new JmlExpressionVisitor(context, M, baseVisitor, TranslationMode.ASSUME, oldVars, this.returnVar, currentMethod);
            JCExpression invCopy = ev.copy(expression);
            oldVars.putAll(ev.getOldVars());
            oldInits = oldInits.appendList(ev.getOldInits());
            invariantAssume = invariantAssume.prependList(ev.getNeededVariableDefs());
            invariantAssume = invariantAssume.appendList(ev.getNewStatements());
            invariantAssume = invariantAssume.append(TranslationUtils.makeAssumeOrAssertStatement(invCopy, TranslationMode.ASSUME));
        }

        List< JCStatement> l = List.nil();

        JCReturn returnStmt = null;
        if(returnVar != null) {
            returnStmt = M.Return(M.Ident(returnVar));
        }

        List<JCStatement> body = List.nil();

        if(that.body != null) {
            body = transformBody(that.body.getStatements());
        }

        //If this is a constructor and this() or super() is called they have to be the first statement
        if(body.size() > 0) {
            if(body.get(0) instanceof JCExpressionStatement) {
                JCExpressionStatement stmt = (JCExpressionStatement)body.get(0);
                if(stmt.expr instanceof JCMethodInvocation) {
                    JCMethodInvocation thisCall = (JCMethodInvocation)stmt.expr;
                    if(thisCall.meth instanceof JCIdent) {
                        Name name = ((JCIdent) thisCall.meth).getName();
                        if(name.toString().equals("this") || name.toString().equals("super")) {
                            l = l.append(body.head);
                            body = body.tail;
                        }
                    }
                }
            }
        }

        JCTry bodyTry = M.Try(M.Block(0L, body),
                List.of(
                        M.Catch(catchVarb, M.Block(0L, List.nil()))
                ),
                null);

        //assume invariants
        long check = that.getModifiers().flags & 8L;
        if(check == 0) {
            l = l.append(M.Block(0L, invariantAssume));
        }

        if(reqCases.size() > 1) {
            l = l.append(specCaseID);
            for(int i = 0; i < reqCases.size(); ++i) {
                if (reqCases.get(i).size() > 0) {
                    JCBlock b = M.Block(0L, reqCases.get(i));
                    JCIf ifstatement = M.If(treeutils.makeEquality(Position.NOPOS, M.Literal(i), M.Ident(specCaseID)), b, null);
                    l = l.append(ifstatement);
                }
            }
        } else if (reqCases.size() == 1) {
            l = l.appendList(reqCases.get(0));
        }

        //adding the variable for old clauses
        for(JCVariableDecl variableDecl : oldVars.values()) {
            l = l.append(variableDecl);
        }

        for(JCStatement oldInit : oldInits) {
            l = l.append(oldInit);
        }

        if(returnVar != null) {
            l = l.append(returnVar);
        }
        l = l.append(bodyTry);


        if(ensCases.size() > 1) {
            for(int i = 0; i < ensCases.size(); ++i) {
                if (ensCases.get(i).size() > 0) {
                    JCBlock b = M.Block(0L, ensCases.get(i));
                    JCIf ifstatement = M.If(treeutils.makeEquality(Position.NOPOS, M.Literal(i), M.Ident(specCaseID)), b, null);
                    l = l.append(ifstatement);
                }
            }
        } else if (ensCases.size() == 1) {
            l = l.appendList(ensCases.get(0));
        }

        //assert invariants
        if(check == 0) {
            l = l.append(M.Block(0L, invariantAssert));
        }

        if(returnStmt != null) {
            l = l.append(returnStmt);
        }

        currentMethod.body = M.Block(0L, l);

        currentMethod.methodSpecsCombined = null;
        currentMethod.cases = null;
        ensCases = List.nil();
        reqCases = List.nil();
        combinedNewEnsStatements = List.nil();
        combinedNewReqStatements = List.nil();

        return currentMethod;
    }

    private List<JCStatement> transformBody(List<JCStatement> oBody) {
        List<JCStatement> body = List.nil();
        for(JCStatement st : oBody) {
            if(!st.toString().equals("super();")) {
                JmlExpressionVisitor ev = new JmlExpressionVisitor(context, M, baseVisitor, translationMode, oldVars, this.returnVar, currentMethod);
                if (currentAssignable == null) {
                    currentAssignable = List.of(M.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING));
                }
                ev.setCurrentAssignable(currentAssignable);
                JCStatement copy = ev.copy(st);
                if (ev.getNewStatements().size() == 0) {
                    body = body.append(copy);
                } else {
                    body = body.appendList(ev.getNewStatements());
                }
            }
        }
        return body;
    }

    public JCTree visitJmlMethodDeclBugfix(JmlMethodDecl that, Void p) {
        JmlMethodDecl copy = (JmlMethodDecl)visitMethodWithoutBody(that, p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;
        //copy.cases = (JmlMethodSpecs)this.copy((JCTree)that.cases, (Object)p);
        copy.methodSpecsCombined = JmlSpecs.copy(that.methodSpecsCombined, p, this);
        copy.cases = (JmlMethodSpecs)copy.methodSpecsCombined.cases.clone();
        copy.type = that.type;
        return copy;
    }

    public JCTree visitMethodWithoutBody(MethodTree node, Void p) {
        JCMethodDecl t = (JCMethodDecl)node;
        JCModifiers mods = (JCModifiers)this.copy((JCTree)t.mods, p);
        JCExpression restype = (JCExpression)this.copy((JCTree)t.restype, p);
        List<JCTypeParameter> typarams = this.copy(t.typarams, p);
        List<JCVariableDecl> params = this.copy(t.params, p);
        JCVariableDecl recvparam = (JCVariableDecl)this.copy((JCTree)t.recvparam, p);
        List<JCExpression> thrown = this.copy(t.thrown, p);
        JCBlock body = M.Block(0L, List.nil());
        JCExpression defaultValue = (JCExpression)this.copy((JCTree)t.defaultValue, p);
        return this.M.at(t.pos).MethodDef(mods, t.name, restype, typarams, recvparam, params, thrown, body, defaultValue);
    }

    private JCLiteral getLiteralForType(Type t) {
        if(t.getTag().equals(TypeTag.INT)) {
            return M.Literal(0);
        }
        if(t.getTag().equals(TypeTag.LONG)) {
            return M.Literal(0);
        }
        if(t.getTag().equals(TypeTag.DOUBLE)) {
            return M.Literal(0.0);
        }
        if(t.getTag().equals(TypeTag.FLOAT)) {
            return M.Literal(0.0f);
        }
        if(t.getTag().equals(TypeTag.SHORT)) {
            return M.Literal(0);
        }
        if(t.getTag().equals(TypeTag.BOOLEAN)) {
            return M.Literal(true);
        }
        if(t.getTag().equals(TypeTag.CHAR)) {
            return M.Literal(0);
        }
        return treeutils.nullLit;
    }
}
