package nl.ou.im9906;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static nl.ou.im9906.ReflectionUtils.isPowerOfTwo;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThan;
import static org.hamcrest.Matchers.greaterThanOrEqualTo;
import static org.hamcrest.Matchers.lessThan;
import static org.hamcrest.Matchers.lessThanOrEqualTo;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link VerifiedIdentityHashMap#capacity(int)} method.
 */
public class IdentityHashMapCapacityTest {

    private VerifiedIdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        // Create an instance of the VerifiedIdentityHashMap
        map = new VerifiedIdentityHashMap<>();
    }

    /**
     * Tests if the result is MAXIMUM_CAPACITY in case of a too large input.
     * <p/>
     * The JML specification to test:
     * <pre>
     *   requires
     *     expectedMaxSize > MAXIMUM_CAPACITY / 3;
     *   ensures
     *     \result == MAXIMUM_CAPACITY;
     * </pre>
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     * @throws InvocationTargetException if an exception occured during the invocation of the capacity method
     */
    @Test
    public void testCapacityNormalBehaviourLargeInput()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        final int max = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");

        int capacity = (int) invokeMethodWithParams(map, "capacity", (max / 3 + 1));
        assertThat(capacity, is(max));
        capacity = (int) invokeMethodWithParams(map, "capacity", Integer.MAX_VALUE);
        assertThat(capacity, is(max));
        capacity = (int) invokeMethodWithParams(map, "capacity", 1431655768);
        assertThat(capacity, is(max));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Assert that the method is pure.
        assertIsPureMethod(map, "capacity", Integer.MAX_VALUE);
    }

    /**
     * Tests the result if input is within MIN-MAX boundaries.
     * <p/>
     * The JML specification to test:
     * <pre>
     @   requires
     @     expectedMaxSize <= MAXIMUM_CAPACITY / (\bigint)3 &&
     @     expectedMaxSize > (\bigint)2 * MINIMUM_CAPACITY / 3;
     @   ensures
     @     \result <= (\bigint)3 * expectedMaxSize &&
     @     2 * \result > (\bigint)3 * expectedMaxSize;
     @   ensures
     @     (\exists \bigint i;
     @       0 <= i < \result;
     @       \dl_pow(2, i) == \result); // result is a power of two
     * </pre>
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     * @throws InvocationTargetException if an exception occured during the invocation of the capacity method
     */
    @Test
    public void testCapacityNormalBehaviourCapacityBetweenMinAndMaxCapacity()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        final int maximum_capacity = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");

        for (int expectedMaxSize = 3; expectedMaxSize < (maximum_capacity * 2) / 3; expectedMaxSize *= 3) {
            // Assert result value
            int capacity = (int) invokeMethodWithParams(map, "capacity", expectedMaxSize);
            final int min = expectedMaxSize * 3 / 2;
            final int max = expectedMaxSize * 3;
            assertThat(capacity, greaterThan(min));
            assertThat(capacity, lessThanOrEqualTo(max));
            assertThat(isPowerOfTwo(capacity), is(true));

            // Assert that the method is pure.
            assertIsPureMethod(map, "capacity", expectedMaxSize);

            // Test if the class invariants hold (postcondition)
            assertClassInvariants(map);
        }
    }

    /**
     * Tests the result if input is too small.
     * <p/>
     * The JML specification to test:
     * <pre>
     @   requires
     @     expectedMaxSize <= MAXIMUM_CAPACITY / (\bigint)3 &&
     @     expectedMaxSize <= (\bigint)2 * MINIMUM_CAPACITY / 3;
     @   ensures
     @     \result == MINIMUM_CAPACITY;
     * </pre>
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     * @throws InvocationTargetException if an exception occured during the invocation of the capacity method
     */
    @Test
    public void testCapacityNormalBehaviourSmallInput()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        final int min = (int) getValueByFieldName(map, "MINIMUM_CAPACITY");

        int capacity = (int) invokeMethodWithParams(map, "capacity", Integer.MIN_VALUE);
        assertThat(capacity, is(min));
        capacity = (int) invokeMethodWithParams(map, "capacity", -1);
        assertThat(capacity, is(min));
        capacity = (int) invokeMethodWithParams(map, "capacity", 0);
        assertThat(capacity, is(min));
        capacity = (int) invokeMethodWithParams(map, "capacity", 2);
        assertThat(capacity, is(min));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Assert that the method is pure.
        assertIsPureMethod(map, "capacity", 0);
    }

}
