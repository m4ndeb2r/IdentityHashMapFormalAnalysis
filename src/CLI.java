import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.Factory;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import picocli.CommandLine;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import static picocli.CommandLine.*;

/**
 * Created by jklamroth on 1/15/19.
 */

@Command(name = "openJBMC", header = "@|bold openJBMC Bounded Model checking for JML|@")
public class CLI implements Runnable {

    public static final String RESET = "\033[0m";  // Text Reset
    public static final String RED_BOLD = "\033[1;31m";    // RED
    public static final String GREEN_BOLD = "\033[1;32m";  // GREEN

    @Option(names = {"-kt", "-keepTranslation"}, description = "Keep the temporary file which contains the translation of the given file.")
    boolean keepTranslation = false;

    @Option(names = {"-va", "-verifyAll"}, description = "Verify all functions not just one.")
    boolean verifyAll = false;

    @Parameters(index="0", arity = "1", description = "The file containing methods to be verified.")
    String fileName = null;

    @Parameters(index="1", arity = "0..1", description = "The method to be verified. If not provided -va is automatically added.")
    String functionName = null;

    @Option(names = {"-df", "-dontFilter"}, description = "If set all JBMC output is printed.")
    boolean filterOutput = true;

    @Option(names = {"-j", "-jbmcOptions"}, description = "Options to be passed to jbmc.")
    List<String> jbmcOptions = new ArrayList<>();

    @Option(names = {"-h", "-help"}, usageHelp = true,
            description = "Print usage help and exit.")
    boolean usageHelpRequested;

    File tmpFolder = null;

    @Override
    public void run() {
        translateAndRunJBMC();
    }

    public static String translate(File file) throws Exception {
        String[] args = {file.getAbsolutePath()};
        return translate(args);
    }

    public static String translate(String[] args) throws Exception {

        IAPI api = Factory.makeAPI();
        java.util.List<JmlTree.JmlCompilationUnit> cu = api.parseFiles(args);
        int a = api.typecheck(cu);
        if(a != 0) {
            System.out.println("OpenJml parser Error.");
            return null;
        }
        Context ctx = api.context();


        for (JmlTree.JmlCompilationUnit it : cu) {
            //System.out.println(api.prettyPrint(rewriteRAC(it, ctx)));
            return api.prettyPrint(rewriteAssert(it, ctx));
        }
        return null;
    }

    public void translateAndRunJBMC() {

        File tmpFile = null;
        try {
            File f = new File(fileName);
            if(!f.exists()) {
                System.out.println("Could not find file " + f);
                return;
            }
            tmpFolder = new File(f.getParentFile(), "tmp");
            tmpFolder.mkdirs();
            tmpFile = new File(tmpFolder, f.getName());
            Files.copy(f.toPath(), tmpFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
            createCProverFolder(tmpFile.getAbsolutePath());
            if(!copyJBMC()) {
                cleanUp();
                return;
            }
            String translation = translate(tmpFile);
            //Files.copy(f.toPath(), new File(fileName.replace(".java", "tmp.java")).toPath(), StandardCopyOption.REPLACE_EXISTING);
            //String name = f.getName().substring(0, f.getName().indexOf("."));
            //TODO This is not always sound!!
            //translation = translation.replaceAll(name, name + "tmp");
            Files.write(tmpFile.toPath(), translation.getBytes(), StandardOpenOption.CREATE);
        } catch (Exception e) {
            cleanUp();
            e.printStackTrace();
            return;
        }

        try {
            Runtime rt = Runtime.getRuntime();
            String[] commands = {"javac", tmpFile.getPath(), "-cp", tmpFile.getParent()};
            System.out.println("Compiling translated file: " + Arrays.toString(commands));
            Process proc = rt.exec(commands);
            proc.waitFor();


            BufferedReader stdInput = new BufferedReader(new
                    InputStreamReader(proc.getInputStream()));

            BufferedReader stdError = new BufferedReader(new
                    InputStreamReader(proc.getErrorStream()));

            // read the output from the command
            String s = stdInput.readLine();
            if (s != null) {
                System.out.println("Error compiling file: " + tmpFile.getPath());
                while (s != null) {
                    System.out.println(s);
                    s = stdInput.readLine();
                }
                return;
            }
            s = stdError.readLine();
            if (s != null) {
                System.out.println("Error compiling file: " + tmpFile.getPath());
                while (s != null) {
                    System.out.println(s);
                    s = stdError.readLine();
                }
                return;
            }

            List<String> functionNames = new ArrayList<>();
            functionNames.addAll(FunctionNameVisitor.parseFile(fileName));
            if(functionName != null) {
                functionNames = functionNames.stream().filter(f -> f.endsWith("." + functionName)).collect(Collectors.toList());
                if(functionNames.size() == 0) {
                    System.out.println("Function " + functionName + " could not be found in the specified file.");
                    return;
                }
            }

            for(String functionName : functionNames) {
                //functionName = tmpFile.getName().replace(".java", "") + "." + functionName;
                runJBMC(tmpFile, functionName);
            }
        } catch (IOException e) {
            System.out.println("Error running jbmc.");
            e.printStackTrace();
        } catch (InterruptedException e) {
            System.out.println("Error. Jbmc got interrupted.");
            e.printStackTrace();
        }
        //cleanUp();
    }

    private List<String> prepareJBMCOptions(List<String> options) {
        List<String> res = new ArrayList<>();
        for(String s : options) {
            for(String o : s.split(" "))
            res.add(o);
        }
        return res;
    }

    public void runJBMC(File tmpFile, String functionName) {
        try {
            System.out.println("Running jbmc for function: " + functionName);
            //commands = new String[] {"jbmc", tmpFile.getAbsolutePath().replace(".java", ".class")};
            String classFile = tmpFile.getPath().replace(".java", ".class");

            ArrayList<String> tmp = new ArrayList<>();
            tmp.add(tmpFolder.getAbsolutePath() + File.separator + "jbmc");
            tmp.add(classFile);
            tmp.add("--function");
            tmp.add(functionName);
            jbmcOptions = prepareJBMCOptions(jbmcOptions);
            tmp.addAll(jbmcOptions);
            String[] commands = new String[tmp.size()];
            commands = tmp.toArray(commands);

            Runtime rt = Runtime.getRuntime();
            rt.addShutdownHook(new Thread(() -> {cleanUp();}));
            Process proc = rt.exec(commands);
            proc.waitFor();

            BufferedReader stdInput = new BufferedReader(new
                    InputStreamReader(proc.getInputStream()));

            BufferedReader stdError = new BufferedReader(new
                    InputStreamReader(proc.getErrorStream()));

            String s = stdInput.readLine();
            String out = "";
            String fullOut = "";
            if (s != null) {
                out += "JBMC Output" + (filterOutput ? " (filtered)" : "") + " for file: " + tmpFile.getPath().replace(".java", ".class") + " with function " + functionName + "\n";
                fullOut += "JBMC Output for file: " + tmpFile.getPath().replace(".java", ".class") + " with function " + functionName + "\n";
                while (s != null) {
                    if (!filterOutput || (s.contains("**") || s.contains("FAILURE") || s.contains("VERIFICATION"))) {
                        if(s.contains("FAILED")) {
                            out += RED_BOLD + s +  RESET + "\n";
                        } else if(s.contains("VERIFICATION")) {
                            out += GREEN_BOLD + s +  RESET + "\n";
                        } else {
                            out += s + "\n";
                        }
                    }
                    fullOut += s + "\n";
                    s = stdInput.readLine();
                }
                s = stdError.readLine();
                while (s != null) {
                    if (!filterOutput || (s.contains("**") || s.contains("FAILURE") || s.contains("VERIFICATION"))) {
                        out += s + "\n";
                    }
                    fullOut += s + "\n";
                    s = stdError.readLine();
                }
                if (!out.contains("VERIFICATION") && !out.contains("FAILURE")) {

                    System.out.println(fullOut);
                } else {
                    System.out.println(out);
                }
            }
        } catch (Exception e) {
            System.out.println("Error running jbmc.");
            e.printStackTrace();
            return;
        }
    }

    private void createCProverFolder(String fileName) {
        File f = new File(fileName);
        File dir = new File(f.getParent() + File.separator + "org" + File.separator + "cprover");
        System.out.println("Copying CProver.java to " + dir.getAbsolutePath());
        dir.mkdirs();
        try {
            InputStream is = Main.class.getResourceAsStream("CProver.java");
            String content = convertStreamToString(is);
            File to = new File(dir.toPath() + File.separator + "CProver.java");
            Files.write(to.toPath(), content.getBytes());
        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException("Error trying to copy CProver.java");
        }
    }

    private boolean copyJBMC() {
        try {
            InputStream is = Main.class.getResourceAsStream("jbmc");
            File to = new File(tmpFolder.getAbsolutePath() + File.separator + "jbmc");
            FileOutputStream buffer = new FileOutputStream(to.getAbsoluteFile());
            int nRead;
            byte[] data = new byte[1024];
            while ((nRead = is.read(data, 0, data.length)) != -1) {
                buffer.write(data, 0, nRead);
            }
            buffer.flush();
            buffer.close();
            is.close();

            ArrayList<String> tmp = new ArrayList<>();
            tmp.add("chmod");
            tmp.add("+x");
            tmp.add(tmpFolder.getAbsolutePath() + File.separator + "jbmc");
            String[] commandsChmod = new String[tmp.size()];
            commandsChmod = tmp.toArray(commandsChmod);

            Runtime rt = Runtime.getRuntime();
            rt.addShutdownHook(new Thread(() -> {cleanUp();}));
            Process proc = rt.exec(commandsChmod);
            proc.waitFor();
        } catch (IOException e) {
            System.out.println("Could not copy jbmc.");
            return false;
        } catch (InterruptedException e) {
            System.out.println("Could not copy jbmc.");
            return false;
        }
        return true;

    }

    String convertStreamToString(java.io.InputStream is) {
        java.util.Scanner s = new java.util.Scanner(is).useDelimiter("\\A");
        return s.hasNext() ? s.next() : "";
    }

    private void cleanUp() {
//        try {
//            if(!keepTranslation) {
//                Files.delete(new File(tmpFolder, new File(fileName).getName()).toPath());
//            }
//            String parent = tmpFolder.getAbsolutePath();
//            Files.delete(new File(parent + File.separator + "org" + File.separator + "cprover" + File.separator + "CProver.java").toPath());
//            Files.delete(new File(parent + File.separator + "org" + File.separator + "cprover" + File.separator + "CProver.class").toPath());
//            Files.delete(new File(parent + File.separator + "org" + File.separator + "cprover").toPath());
//            Files.delete(new File(parent + File.separator + "org").toPath());
//            Files.delete(new File(fileName.replace(".java", ".class")).toPath());
//            Files.delete(new File(fileName.replace(".java", "$ReturnException.class")).toPath());
//        } catch (IOException e) {
//            e.printStackTrace();
//        }
        deleteFolder(tmpFolder);
        if(!keepTranslation) {
            try {
                if(tmpFolder.exists()) {
                    Files.delete(tmpFolder.toPath());
                }
            } catch (IOException e) {
                //System.out.println("Could not delete tmp folder.");
            }
        }
    }

    private void deleteFolder(File folder) {
        File[] tmpFiles = folder.listFiles();
        for(File f : tmpFiles) {
            if(!keepTranslation || !f.getName().endsWith(new File(fileName).getName())) {
                if (f.isDirectory()) {
                    deleteFolder(f);
                }
                try {
                    if(f.exists()) {
                        Files.delete(f.toPath());
                    }
                } catch (IOException ex) {
                    //System.out.println("Could not delete temporary file: " + f.getAbsolutePath());
                }
            }
        }
    }

    JCTree rewriteRAC(JmlTree.JmlCompilationUnit cu, Context context) {
        JmlAssertionAdder jaa = new JmlAssertionAdder(context, false, true);
        context.dump();
        return jaa.convert(cu);
    }

    static JCTree rewriteAssert(JmlTree.JmlCompilationUnit cu, Context context) {
        context.dump();
        return cu.accept(new BaseVisitor(context, JmlTree.Maker.instance(context)), null);
    }
}

class FunctionNameVisitor extends JmlTreeScanner {
    static private List<String> functionNames = new ArrayList();

    @Override
    public void visitJmlMethodDecl(JmlTree.JmlMethodDecl that) {
        String f = that.sym.owner.toString() + "." + that.getName().toString();
        if(!f.contains("<init>")) {
            functionNames.add(f);
        }
        super.visitJmlMethodDecl(that);
    }

    public static List<String> parseFile(String fileName) {
        functionNames = new ArrayList();
        try {
            String[] args = {fileName};
            IAPI api = Factory.makeAPI();
            java.util.List<JmlTree.JmlCompilationUnit> cu = api.parseFiles(args);

            Context ctx = api.context();
            FunctionNameVisitor fnv = new FunctionNameVisitor();
            for (JmlTree.JmlCompilationUnit it : cu) {
                ctx.dump();
                it.accept(fnv);
            }
        } catch (Exception e) {
            System.out.println("error parsing for method names");
        }
        return functionNames;
    }
}
