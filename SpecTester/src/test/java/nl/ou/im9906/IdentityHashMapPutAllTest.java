package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertAssignableClause;
import static nl.ou.im9906.MethodTestHelper.assertAssignableNothingClause;
import static org.junit.Assert.fail;

/**
 * Tests the JML specifications of the {@link VerifiedIdentityHashMap#putAll(Map)}
 * method.
 *
 * Note: the JML for this method is incomplete, and, therefore, so is this test.
 * Note 2: the putAll method is not verified with KeY.
 */
public class IdentityHashMapPutAllTest {

    // The test subject
    private VerifiedIdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new VerifiedIdentityHashMap<>();
    }

    /**
     * Tests if a {@link NullPointerException} is thrown when a {@code null} is passed
     * as parameter to the putAll method of the {@link VerifiedIdentityHashMap}.
     * <p/>
     * JML specification to test:
     * <pre>
     *   requires
     *     m == null;
     *   assignable
     *     \nothing;
     *   signals_only
     *     NullPointerException;
     *   signals
     *     (NullPointerException e) true;
     * </pre>
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    @Test
    public void testPutAllExceptionalBehaviour()
            throws NoSuchMethodException, NoSuchFieldException,
            IllegalAccessException, InvocationTargetException,
            NoSuchClassException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Check the assignable clause
        assertAssignableNothingClause(map, "putAll", new Object[]{null});

        // This should throw a NullPointerException
        try {
            map.putAll(null);
            fail("Expected a NullPointerException");
        } catch (NullPointerException e) {
            // Test if the class invariants hold (postcondition)
            assertClassInvariants(map);
        }

    }

    /**
     * TODO: This test is still incomplete. So is the JML. Furthermore, the putAll method is not verified with KeY.
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    @Test
    public void testPutAllNormalBehaviour()
            throws IllegalAccessException, NoSuchFieldException,
            NoSuchMethodException, NoSuchClassException {
        // TODO: we only check the assignable clause here now. This test is, therefore incomplete.

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Check the JML assignable clause
        final Map<String, String>[] params = new Map[1];
        params[0] = new HashMap<>();
        params[0].put("aKey", "aValue");
        assertAssignableClause(map, "putAll", params,
                new String[]{"table", "size", "modCount"}
        );

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);
    }

}
