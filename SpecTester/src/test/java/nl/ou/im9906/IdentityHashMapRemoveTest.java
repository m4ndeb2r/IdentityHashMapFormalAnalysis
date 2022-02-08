package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertAssignableClause;
import static nl.ou.im9906.MethodTestHelper.assertAssignableNothingClause;
import static nl.ou.im9906.MethodTestHelper.keyExistsInTable;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.not;
import static org.hamcrest.Matchers.nullValue;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link VerifiedIdentityHashMap#remove(Object)}
 * method.
 *
 * Note: the remove method is not verified by KeY, and the JML might, therefore, be
 * incomplete or incorrect. And, indeed, so might this test.
 */
public class IdentityHashMapRemoveTest {

    private VerifiedIdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new VerifiedIdentityHashMap<>();
    }

    /**
     * Tests the normal behaviour the method {@link VerifiedIdentityHashMap#remove(Object)}
     * when the key to be removed exists.
     * <p/>
     * JML to test:
     * <pre>
     *   assignable
     *     size, table, modCount;
     *   ensures
     *     // Size is subtracted by 1
     *     size == \old(size) - 1 &&
     *
     *     // modCount is changed
     *     modCount != \old(modCount) &&
     *
     *     // Result is the removed value
     *     (\forall int j;
     *       0 <= j < \old(table.length) / 2;
     *       \old(table[j*2]) == maskNull(key) ==> \result == \old(table[j*2 + 1])) &&
     *
     *     // All not-to-be-removed elements are still present
     *     (\forall int i;
     *       0 <= i < \old(table.length) / 2;
     *       \old(table[i * 2]) != maskNull(key) ==>
     *         (\exists int j;
     *            0 <= j < table.length / 2;
     *            table[j*2] == \old(table[i * 2]) && table[j*2+1] == \old(table[i * 2+1]))) &&
     *
     *     // The deleted key no longer exists in the table
     *     !(\exists int i;
     *        0 <= i < table.length / 2;
     *        table[i*2] == maskNull(key));
     * </pre>
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void testRemoveNormalBehaviourWhenKeyExists()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {

        final String key1 = null; // A null key to test the maskNull(key) spec.
        final Object maskedNullKey = getValueByFieldName(map, "NULL_KEY");
        map.put(key1, "Value1");
        final String key2 = "Key2";
        map.put(key2, "Value2");
        final String key3 = "Key3";
        map.put(key3, "Value3");

        // Check class invariants (precondition)
        assertClassInvariants(map);

        int oldSize = (int) getValueByFieldName(map, "size");
        int oldModCount = (int) getValueByFieldName(map, "modCount");

        // Remove key1 and check the assignable clause for the remove method
        assertAssignableClauseForRemove(key1);
        // Assert postcondition
        assertThat(map.size(), is(2));
        assertThat((int) getValueByFieldName(map, "size"), is(oldSize - 1));
        assertThat((int) getValueByFieldName(map, "modCount"), not(is(oldModCount)));
        assertKeyNotInTable(maskedNullKey);
        assertAllFoundInTable(key2, key3);

        oldSize = (int) getValueByFieldName(map, "size");
        oldModCount = (int) getValueByFieldName(map, "modCount");

        // Remove key2 and check return value
        assertThat((String) invokeMethodWithParams(map, "remove", key2), is("Value2"));
        // Assert postcondition
        assertThat(map.size(), is(1));
        assertThat((int) getValueByFieldName(map, "size"), is(oldSize - 1));
        assertThat((int) getValueByFieldName(map, "modCount"), not(is(oldModCount)));
        assertKeyNotInTable(key2);
        assertAllFoundInTable(key3);

        // Check class invariants (postcondition)
        assertClassInvariants(map);
    }

    /**
     * Tests the normal behaviour the method {@link VerifiedIdentityHashMap#remove(Object)}
     * when the key to be removed does not exitst.
     * <p/>
     * JML to test:
     * <pre>
     @   assignable
     @     \nothing;
     @   ensures
     @     \result == null &&
     @     table.length == \old(table.length);
     * </pre>
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void testRemoveNormalBehaviourWhenKeyDoesNotExist()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {

        final String key1 = "Key1";
        map.put(key1, "Value1");

        final String key2 = "Key2";
        map.put(key2, "Value2");

        final Object key3 = null; // A null key to test the maskNull(key) spec.
        final Object maskedNullKey = getValueByFieldName(map, "NULL_KEY");
        map.put(key3, "Value3");

        // Check class invariants (pre-condition)
        assertClassInvariants(map);

        int oldSize = (int) getValueByFieldName(map, "size");
        int oldModCount = (int) getValueByFieldName(map, "modCount");

        // Check the assignable clause: no changes allowed when key does not exist
        assertAssignableNothingClause(map, "remove", new String[]{"unknownKey"});

        // Assert postcondition
        assertThat(map.size(), is(3));
        assertThat((int) getValueByFieldName(map, "size"), is(oldSize));
        assertThat((int) getValueByFieldName(map, "modCount"), is(oldModCount));
        assertThat((String) invokeMethodWithParams(map, "remove", "unknownKey"), nullValue());
        assertAllFoundInTable(key1, key2, maskedNullKey);

        // Check class invariants (post-condition)
        assertClassInvariants(map);
    }

    // Check assignable clause: assignable szie, table, modCount
    private void assertAssignableClauseForRemove(String key)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException {
        assertAssignableClause(
                map,
                "remove",
                new String[]{key},
                new String[]{"size", "table", "modCount"}
        );
    }

    // Check that the specified key is not present in the table
    private void assertKeyNotInTable(Object key)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException {
        assertThat(keyExistsInTable(map, key), is (false));
    }

    // Check that the specified key is not present in the table
    private void assertAllFoundInTable(Object... keys)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException {
        for (Object key : keys) {
            assertThat(keyExistsInTable(map, key), is(true));
        }
    }

}
