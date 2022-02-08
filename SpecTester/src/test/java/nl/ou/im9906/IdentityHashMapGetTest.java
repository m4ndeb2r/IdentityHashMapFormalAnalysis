package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.MethodTestHelper.mappingExistsInTable;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link VerifiedIdentityHashMap#get(Object)}
 * method.
 */
public class IdentityHashMapGetTest {

    private Object maskedNullKey;

    // The test subject
    private VerifiedIdentityHashMap<Object, Object> map;

    @Before
    public void setUp()
            throws NoSuchFieldException, IllegalAccessException {
        map = new VerifiedIdentityHashMap<>();
        maskedNullKey = getValueByFieldName(map, "NULL_KEY");
    }

    /**
     * Test if the normal behaviour of the {@link VerifiedIdentityHashMap#get(Object)} method
     * for several cases. Also, the purity of the method is tested.
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    @Test
    public void testGetPostcondition()
            throws InvocationTargetException, NoSuchMethodException,
            IllegalAccessException, NoSuchFieldException,
            NoSuchClassException {
        assertGetPostConditionForNonNullResult(map);
        assertGetPostConditionForNullResult(map);
    }

    /**
     * Tests the normal behaviour of the {@link VerifiedIdentityHashMap#get(Object)}
     * method when a non-{@code null} value is found and returned as a result.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertGetPostConditionForNonNullResult(VerifiedIdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        final String key = "key";
        final String val1 = "val1";
        final String val2 = "val2";

        map.put(key, val1);
        map.put(null, val2);

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Assert that the following postcondition holds:
        //   \result != null <==>
        //       (\exists int i;
        //           0 <= i < table.length - 1;
        //           i % 2 == 0 && table[i] == maskNull(key) && \result == table[i + 1]);
        final boolean foundVal1 = mappingExistsInTable(map, key, val1);
        assertThat(map.get(key) != null && foundVal1, is(true));
        final boolean foundVal2 = mappingExistsInTable(map, maskedNullKey, val2);
        assertThat(map.get(null) != null && foundVal2, is(true));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the get method is pure
        assertIsPureMethod(map, "get", key);
    }

    /**
     * Checks if the postcondition for the get method of the {@link VerifiedIdentityHashMap} holds
     * when a {@code null} value is found and returned as a result.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertGetPostConditionForNullResult(VerifiedIdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        // Assert that the following postcondition holds:
        //     \result == null <==>
        //        (!(\exists int i;
        //           0 <= i < table.length - 1 ;
        //           i % 2 == 0 && table[i] == maskNull(key)) ||
        //        (\exists int i;
        //           0 <= i < table.length - 1 ;
        //           i % 2 == 0 && table[i] == maskNull(key) && table[i + 1] == null)
        //        );
        assertGetPostConditionKeyNotFound(map);
        assertGetPostConditionValueNull(map);
    }

    /**
     * Checks if the postcondition for the get method of the {@link VerifiedIdentityHashMap} holds
     * when a {@code null} value is found and returned as a result, because the key is not
     * found.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertGetPostConditionKeyNotFound(VerifiedIdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        final String key = "aKey";
        final String anotherKey = new String("aKey");
        final String val = "aValue";
        map.put(key, val);

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        final boolean valueFound = mappingExistsInTable(map, anotherKey, val);
        assertThat(map.get(anotherKey) == null, is(true));
        assertThat(valueFound, is(false));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the get method is pure
        assertIsPureMethod(map, "get", key);
    }

    /**
     * Checks if the postcondition for the get method of the {@link VerifiedIdentityHashMap} holds
     * when a {@code null} value is found and returned as a result, because however the key
     * is found, the value is actually {@code null}.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertGetPostConditionValueNull(VerifiedIdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException {
        final String key = "KEY";
        final String val = null;
        map.put(key, val);

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        final boolean valueFound = mappingExistsInTable(map, key, val);
        assertThat(map.get(key) == null, is(true));
        assertThat(valueFound, is(true));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the get method is pure
        assertIsPureMethod(map, "get", key);
    }

}
