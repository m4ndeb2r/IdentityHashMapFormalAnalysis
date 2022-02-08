package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.MethodTestHelper.mappingExistsInTable;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link VerifiedIdentityHashMap#containsMapping(Object, Object)}
 * method.
 */
public class IdentityHashMapContainsMappingTest {

    // The test subject
    private VerifiedIdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new VerifiedIdentityHashMap<>();
    }

    /**
     * Checks if the normal behaviour of the method {@link VerifiedIdentityHashMap#containsMapping(Object, Object).
     * <p/>
     * Tests the following JML postcondition:
     * <pre>
     *     \result <==> (\exists int i;
     *         0 <= i < table.length / 2;
     *         table[i*2] == maskNull(key) && table[i*2 + 1] == value);
     * </pre>
     * Also tests if the method is pure, and checks if the class invariants hold
     * before and after invocation of the method.
     *
     * @param map the map to call the containsMapping method on
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    @Test
    public void testContainsMappingNormalBehaviour()
            throws InvocationTargetException, NoSuchMethodException,
            IllegalAccessException, NoSuchClassException,
            NoSuchFieldException {
        assertContainsMappingBehaviourFound(map);
        assertContainsNullKeyMappingBehaviourFound(map);
        assertContainsMappingBehaviourNotFound(map);
    }

    /**
     * Checks if the postcondition for the method
     * {@link VerifiedIdentityHashMap#containsMapping(Object, Object)}
     * holds when a mapping with a key null is present in the table.
     *
     * @param map the map to call the containsMapping method on
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertContainsNullKeyMappingBehaviourFound(VerifiedIdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            InvocationTargetException, NoSuchMethodException,
            NoSuchClassException {
        final String key = null; // Note: using null for a key will also test the maskNull(key) spec.
        final Object maskedNullKey = getValueByFieldName(map, "NULL_KEY");
        final String value = "aValue";
        assertThat((Boolean) invokeMethodWithParams(map, "containsMapping", key, value), is(false));

        map.put(key, value);

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Call the method an check the result (postcondition)
        final boolean found = mappingExistsInTable(map, maskedNullKey, value);
        assertThat((Boolean) invokeMethodWithParams(map, "containsMapping", key, value), is(found));
        assertThat(found, is(true));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the containsMapping method is pure
        assertIsPureMethod(map, "containsMapping", key, value);
    }

    /**
     * Checks if the postcondition for the method
     * {@link VerifiedIdentityHashMap#containsMapping(Object, Object)}
     * holds when a mapping is present in the table.
     *
     * @param map the map to call the containsMapping method on
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertContainsMappingBehaviourFound(VerifiedIdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            InvocationTargetException, NoSuchMethodException,
            NoSuchClassException {
        final String key = "aKey";
        final String value = "aValue";
        assertThat((Boolean) invokeMethodWithParams(map, "containsMapping", key, value), is(false));

        map.put(key, value);

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Call the method an check the result (postcondition)
        final boolean found = mappingExistsInTable(map, key, value);
        assertThat((Boolean) invokeMethodWithParams(map, "containsMapping", key, value), is(found));
        assertThat(found, is(true));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the containsMapping method is pure
        assertIsPureMethod(map, "containsMapping", key, value);
    }

    /**
     * Checks if the postcondition for the method
     * {@link VerifiedIdentityHashMap#containsMapping(Object, Object)}
     * holds when a mapping is NOT present in the table.
     *
     * @param map the map to call the containsMapping method on
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertContainsMappingBehaviourNotFound(VerifiedIdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            InvocationTargetException, NoSuchMethodException,
            NoSuchClassException {
        final String key = "aKey";
        final String value = "aValue";
        map.put(key, value);
        final String anotherValue = "anotherValue";

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Call the method an check the result (postcondition)
        final boolean found = mappingExistsInTable(map, key, anotherValue);
        assertThat((Boolean) invokeMethodWithParams(map, "containsMapping", key, anotherValue), is(found));
        assertThat(found, is(false));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the containsMapping method is  pure
        assertIsPureMethod(map, "containsMapping", key, anotherValue);
    }

}
