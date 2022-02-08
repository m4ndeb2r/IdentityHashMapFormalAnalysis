package nl.ou.im9906;

import org.hamcrest.Matcher;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static nl.ou.im9906.ReflectionUtils.isFinal;
import static nl.ou.im9906.ReflectionUtils.isPrimitive;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

public class MethodTestHelper {

    /**
     * Asserts that no fields are assigned a value during the processing of the method under
     * analysis. This conforms to the JML clause: {@code assignable \nothing}. This more or
     * less a purity check for methods. The only difference is that pure methods also
     * conform to the JML clause: {@code \diverges false}.
     * <p/>
     * Example: the JML specification clause {@code assignable \nothing;} for the
     * method under test {@code someMethod}, that expects no input parameters, would be
     * testable by the following call to this method:
     * {@code assertAssignableNothingClause(anObject, "someMethod", new Object[]{});},
     * where {@code anObject} is the object to invoke the method under ananlysis on.
     *
     * @param obj        an object to invoke the method under analysis on
     * @param methodName the method under analysis
     * @param params     the actual parameters that will be passed to the method
     * @throws NoSuchMethodException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    protected static void assertAssignableNothingClause(Object obj, String methodName, Object[] params)
            throws NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        assertAssignableClause(obj, methodName, params, new String[0]);
    }

    /**
     * Asserts that fields that are not assignable according to the JML specification, do
     * not get assigned a new value during the invocation of the method under analysis.
     * <p/>
     * Example: the JML specification clause {@code assignable field1, field2;} for the
     * method under test {@code someMethod}, that expects no input parameters, would be
     * testable by the following call to this method:
     * {@code assertAssignableClause(anObject, "someMethod", new Object[]{}, new String[]{"field1", "field2"});},
     * where {@code anObject} is the object to invoke the method under ananlysis on.
     * <p/>
     * Note 1: {@link InvocationTargetException}s are ignored. It might be the case that during invocation
     * of the method an exception is thrown. This might be expected behaviour; we might be testing
     * the assignable clause for exceptional_bevavior (in terms of JML), and we still want to check
     * the fields, regardless of any exception during invocation.
     * <p/>
     * Note 2: comparison of fields is ideally done shallow (using the '==' operator). However, the use
     * of Reflection is in our way. By retrieving the value of a private primitive field (Field.get()) we
     * always get a fresh object representation ot the primitive of the field value. With every Field.get()
     * we get a new copy (i.e. a new Integer object in case of an int, a new Long object in case of a long,
     * etc.). Therefore, in case of a pri,itive field, every comparison of the old field value and the new
     * field value using the '==' operator would return {@code false}. This is obviously not what we
     * intended. For pragmatic reasons, therefore, we will use the {@link org.hamcrest.Matchers#is(Matcher)}
     * method for primitives.
     * <p/>
     * Note 3: We do not check assignability of incoming parameters. This is not necessary, because
     * Java applies the copy-in parameter mechanism. It is, therefore, impossible to assign a value
     * to the actual parameters passed to the method. Inside the method, a copy of the value is used,
     * and assigning to that copy cannot result in a side effect.
     * <p/>
     * Note 4: We assume a very loose interpretation of the term 'assignable'. Any non-assignable field
     * could be assigned a value and reassigned the original value again after that, and we would not
     * notice.
     *
     * @param obj                  the object to invoke the method under analysis on
     * @param methodName           the method under analysis
     * @param params               the actual parameters that will be passed to the method
     * @param assignableFieldNames the names of the fields in the {@link VerifiedIdentityHashMap}
     *                             that are assignable. Fields with these names will not be
     *                             checked for alteration. All other fields will be checked
     *                             for alteration.
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    protected static void assertAssignableClause(
            final Object obj,
            final String methodName,
            final Object[] params,
            final String[] assignableFieldNames)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {

        // Collect the non-assignable fields from the VerifiedIdentityHashMap, their names,
        // and their original values, before invoking the method under analysis.
        final Field[] fields = obj.getClass().getDeclaredFields();
        final Map<String, Object> oldFieldValues = new HashMap<>();
        for (int i = 0; i < fields.length; i++) {
            // Skip final fields (because they cannot be assigned anyway) as
            // well as the assignable fields (because we do not have to check
            // these).
            final String fieldName = fields[i].getName();
            if (!isFinal(obj, fieldName) && !arrayContains(assignableFieldNames, fieldName)) {
                final Object fieldValue = getValueByFieldName(obj, fieldName);
                oldFieldValues.put(fieldName, fieldValue);
            }
        }

        // Now, invoke the method under analysis.
        try {
            invokeMethodWithParams(obj, methodName, params);
        } catch (InvocationTargetException e) {
            // This might be due to an Exception that is expected in the
            // exceptional_behavior heavy weight specification case of the JML.
            // We still want to check the JML assignable clause. So, let's do
            // nothing, and resume to check the fields and parameters.
        }

        // Check if the fields have not been unexpectedly assigned a value.
        // I.e. (according to our 'loose' interpretation of the term 'assignable')
        // compare the old value with the current value.
        for (String fieldName : oldFieldValues.keySet()) {
            final Object newFieldValue = getValueByFieldName(obj, fieldName);
            final Object oldFieldValue = oldFieldValues.get(fieldName);
            if (isPrimitive(obj, fieldName)) {
                // In case of a primitive field, we cannot use the '==' operator,
                // because getValuesByFieldName returns an object representation
                // of the actual reference to the respective field. We, therefore,
                // use Matchers.is()
                assertOldEqualsNewPrimitive(fieldName, newFieldValue, oldFieldValue);
            } else {
                // In case of a non-primitive field, we can use the '==' operator,
                // because getValuesByFieldName returns the actual reference to the
                // respective object.
                assertOldSameAsNewNonPrimitive(fieldName, newFieldValue, oldFieldValue);
            }
        }
    }

    private static void assertOldSameAsNewNonPrimitive(final String fieldName, final Object newFieldValue, final Object oldFieldValue) {
        final String msg = String.format(
                "Non-primitive, non-assignable field '%s' unexpectedly assigned.",
                fieldName
        );
        assertThat(msg, newFieldValue == oldFieldValue, is(true));
    }

    private static void assertOldEqualsNewPrimitive(final String fieldName, final Object newFieldValue, final Object oldFieldValue) {
        final String msg = String.format(
                "Primitive, non-assignable field '%s' unexpectedly changed.",
                fieldName
        );
        assertThat(msg, newFieldValue, is(oldFieldValue));
    }

    /**
     * Asserts that a method is pure, i.e. does not have any side effect.
     *
     * @param obj        the object to call the method on
     * @param methodName the name of the method we expect to be pure
     * @param params     the actual parameters passed to the method
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     */
    protected static void assertIsPureMethod(Object obj, String methodName, Object... params)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        assertAssignableNothingClause(obj, methodName, params);
    }

    /**
     * Determines whether a specified key-value pair is present in the
     * {@link VerifiedIdentityHashMap}'s table array field.
     *
     * @param map instance of the {@link VerifiedIdentityHashMap} to search in
     * @param key the key to search
     * @param val the value to search
     * @return {@code true} if found, {@code false} otherwise
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    protected static boolean mappingExistsInTable(VerifiedIdentityHashMap<Object, Object> map, Object key, Object val)
            throws NoSuchFieldException, IllegalAccessException {
        if (key == null) {
            throw new IllegalArgumentException("A key cannot be null. Did you mean to pass a masked null key (NULL_KEY)?");
        }
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 0; i < table.length - 1; i += 2) {
            if (table[i] == key && table[i + 1] == val) {
                return true;
            }
        }
        return false;
    }

    /**
     * Determines whether a specified key is present in the {@link VerifiedIdentityHashMap}'s
     * table array field.
     *
     * @param map instance of the {@link VerifiedIdentityHashMap} to search in
     * @param key the key to search
     * @return {@code true} if found, {@code false} otherwise
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    protected static boolean keyExistsInTable(VerifiedIdentityHashMap<?, ?> map, Object key)
            throws NoSuchFieldException, IllegalAccessException {
        if (key == null) {
            throw new IllegalArgumentException("A key cannot be null. Did you mean to pass a masked null key (NULL_KEY)?");
        }
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 0; i < table.length - 1; i += 2) {
            if (table[i] == key) {
                return true;
            }
        }
        return false;
    }

    /**
     * Determines whether a specified value is present in the {@link VerifiedIdentityHashMap}'s
     * table array field. Note: comparison is based on '==' operator.
     *
     * JML (see containsValue contract):
     * <pre>
     *    ensures
     *      \result <==> (\exists int i;
     *          0 <= i < table.length / 2;
     *          table[i*2] != null && table[i*2 + 1] == value);
     * </pre>
     *
     * @param map instance of the {@link VerifiedIdentityHashMap} to search in
     * @param val the value to search
     * @return {@code true} if found, {@code false} otherwise
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    protected static boolean valueExistsInTable(VerifiedIdentityHashMap<?, ?> map, Object val)
            throws NoSuchFieldException, IllegalAccessException {
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 0; i < table.length / 2; i++) {
            if (table[i*2] != null && table[i*2 + 1] == val) {
                return true;
            }
        }
        return false;
    }

    /**
     * Determines whether the specified array contains a value equal to the specified value.
     *
     * @param array the array to search
     * @param value the value to find
     * @param <T>   the type of the values in the array
     * @return {@code true} if an element equal to value was found in array, or {@code false}
     * otherwise.
     */
    private static <T> boolean arrayContains(final T[] array, final T value) {
        for (final T element : array) {
            if (Objects.equals(value, element)) {
                return true;
            }
        }
        return false;
    }
}
