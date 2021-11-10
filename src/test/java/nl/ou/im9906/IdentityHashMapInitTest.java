package nl.ou.im9906;

import org.junit.Test;

import java.lang.reflect.InvocationTargetException;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertAssignableClause;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static nl.ou.im9906.ReflectionUtils.isPowerOfTwo;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThanOrEqualTo;
import static org.hamcrest.Matchers.lessThanOrEqualTo;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link VerifiedIdentityHashMap#init(int)
 * method.
 */
public class IdentityHashMapInitTest {

    // The test subject
    private VerifiedIdentityHashMap<Object, Object> map;

    /**
     * Tests the normal behaviour of the method {@link VerifiedIdentityHashMap#init(int)}.
     * Pre-conditions are: the parameter initCapacity must be a power of 2, and must
     * be a value between MINIMUM_CAPACITY and MAXIMUM_CAPACITY, and size must be 0.
     * Postconditions are: the length of the table array must be 2 * initCapacity, and
     * the size must be unchanged.
     * <p/>
     * Furthermore, it is tested if the class invariant holds as a precondition and
     * as a postcondition of the method call.
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    @Test
    public void testInitNormalBehaviour()
            throws NoSuchMethodException, IllegalAccessException, InvocationTargetException,
            NoSuchFieldException, NoSuchClassException {
        // Small capacity
        map = new VerifiedIdentityHashMap<>();
        assertInitNormalBehaviour((int) getValueByFieldName(map, "MINIMUM_CAPACITY"));

        // Medium capacity
        map = new VerifiedIdentityHashMap<>();
        assertInitNormalBehaviour((int) getValueByFieldName(map, "DEFAULT_CAPACITY"));

        // Large capacity
        map = new VerifiedIdentityHashMap<>();
        assertInitNormalBehaviour(67108864);
    }

    /**
     * Checks the postcondition after invoking the init method of the {@link VerifiedIdentityHashMap} class.
     *
     * @param initCapacity the actual parameter to pass to the init method
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertInitNormalBehaviour(int initCapacity)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException,
            InvocationTargetException, NoSuchClassException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Assert method precondition
        //   requires
        //     MINIMUM_CAPACITY == 4 && 
        //     MAXIMUM_CAPACITY == 536870912 &&
        //     (\exists i;
        //       0 <= i < initCapacity;
        //       \dl_pow(2,i) == initCapacity) &&
        //     initCapacity >= MINIMUM_CAPACITY &&
        //     initCapacity <= MAXIMUM_CAPACITY &&
        //     size == 0;
        assertThat(isPowerOfTwo(initCapacity), is(true));
        assertThat(initCapacity, greaterThanOrEqualTo(4));
        assertThat(initCapacity, lessThanOrEqualTo(536870912));

        // Execute the init method
        invokeMethodWithParams(map, "init", initCapacity);

        // Assert that the JML postcondition of the init method holds:
        //   ensures
        //     table.length == 2 * initCapacity;
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(initCapacity * 2));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Assert that no other fields are assigned a value that "table",
        // validating the JML clause:
        //     \assignable
        //         table.
        assertAssignableClause(map, "init", new Integer[]{initCapacity}, new String[]{"table"});
    }

}
