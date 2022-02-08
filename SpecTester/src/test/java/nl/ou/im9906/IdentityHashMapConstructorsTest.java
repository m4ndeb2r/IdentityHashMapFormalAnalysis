package nl.ou.im9906;

import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.not;
import static org.hamcrest.Matchers.nullValue;
import static org.hamcrest.core.Is.is;
import static org.junit.Assert.fail;

/**
 * Tests the JML specifications of the {@link VerifiedIdentityHashMap}'s constructors.
 *
 * Note: the constructors were NOT verified with KeY.
 */
public class IdentityHashMapConstructorsTest {

    /**
     * Tests the normal behaviour of the default constructor of the {@link VerifiedIdentityHashMap}.
     * The length of the private field table is expected to be 2 * DEFAULT_CAPACITY = 64,
     * and the exptected size of the map is 0.
     * <p/>
     * JML specification to check:
     * <pre>
     *   requires
     *     DEFAULT_CAPACITY == 32
     *   ensures
     *     table != null &&
     *     table.length == (\bigint)2 * DEFAULT_CAPACITY &&
     *     keySet == null &&
     *     values == null &&
     *     entrySet == null &&
     *     modCount == 0 &&
     *     size == 0 &&
     *     (\forall \bigint i; 0 <= i && i < table.length; table[i] == null);
     * </pre>
     * <p/>
     * Obviously, the class invariants must hold after invoking the constructor. This is also
     * checked.
     *
     * @throws NoSuchFieldException   if the expected private field table does not exist
     * @throws IllegalAccessException if it was not possible to get access to the private field
     * @throws NoSuchClassException   if any of the expected (inner) classes does not exist
     */
    @Test
    public void testDefaultConstructorPostCondition()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        // Call default constructor
        final VerifiedIdentityHashMap<Object, Object> map = new VerifiedIdentityHashMap<>();

        // Check post condition
        final int defaultCapacity = (int) getValueByFieldName(map, "DEFAULT_CAPACITY");
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        assertThat(table.length, is(2 * defaultCapacity));
        for (Object element : table) {
            assertThat(element, nullValue());
        }
        assertThat((getValueByFieldName(map, "keySet")), nullValue());
        assertThat((getValueByFieldName(map, "values")), nullValue());
        assertThat((getValueByFieldName(map, "entrySet")), nullValue());
        assertThat(((int) getValueByFieldName(map, "modCount")), is(0));
        assertThat(map.size(), is(0));


        // After invoking the constructor, the class invariants must hold.
        assertClassInvariants(map);
    }

    /**
     * Tests the exceptional behaviour of the constructor of the {@link VerifiedIdentityHashMap}
     * that accepts an expected max size for an argument. When a negative value is passed,
     * an IllegalArgumentException is expected.
     * <p/>
     * JML specification to check:
     * <pre>
     *   requires
     *     expectedMaxSize < 0;
     *   signals_only
     *     IllegalArgumentException;
     *   signals
     *     (IllegalArgumentException e) true;
     * </pre>
     */
    @Test
    public void testConstructorWithPreferredCapacityExceptionalBehaviour() {
        try {
            new VerifiedIdentityHashMap<>(-1);
        } catch (IllegalArgumentException e) {
            return;
        }
        fail("Expected an IllegalArgumentException.");
    }

    /**
     * Tests the normal behaviour of the constructor of the {@link VerifiedIdentityHashMap}
     * that accepts an expected max size for an argument. When a non-negative value
     * is passed, we expect the length of the table array to be determined by the
     * capacity method.
     * <p/>
     * JML specification to check:
     * <pre>
     *   requires
     *     expectedMaxSize >= 0;
     *   ensures
     *     table != null &&
     *     table.length == 2 * capacity(expectedMaxSize) &&
     *     keySet == null &&
     *     values == null &&
     *     entrySet == null &&
     *     modCount == 0 &&
     *     size == 0 &&
     *     (\forall \bigint i; 0 <= i && i < table.length; table[i] == null);
     * </pre>
     * <p/>
     * Obviously, the class invariants must hold after invoking the constructor. This is also
     * checked.
     *
     * @throws NoSuchMethodException
     * @throws InvocationTargetException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     * @throws InstantiationException
     * @throws NoSuchClassException
     */
    @Test
    public void testConstructorWithExpectedMaxSizeNormalBehaviour()
            throws NoSuchMethodException, InvocationTargetException, IllegalAccessException, NoSuchFieldException, InstantiationException, NoSuchClassException {
        VerifiedIdentityHashMap<String, String> map = new VerifiedIdentityHashMap<>(0);
        int capacity = (int) invokeMethodWithParams(map, "capacity", 0);
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        assertThat(table.length, is(2 * capacity));
        for (Object element : table) {
            assertThat(element, nullValue());
        }
        assertThat((getValueByFieldName(map, "keySet")), nullValue());
        assertThat((getValueByFieldName(map, "values")), nullValue());
        assertThat((getValueByFieldName(map, "entrySet")), nullValue());
        assertThat(((int) getValueByFieldName(map, "modCount")), is(0));
        assertThat(map.size(), is(0));

        final int largeInt = Integer.MAX_VALUE / 1024;
        map = new VerifiedIdentityHashMap<>(largeInt);
        capacity = (int) invokeMethodWithParams(map, "capacity", largeInt);
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(2 * capacity));
        assertThat((getValueByFieldName(map, "keySet")), nullValue());
        assertThat((getValueByFieldName(map, "values")), nullValue());
        assertThat((getValueByFieldName(map, "entrySet")), nullValue());
        assertThat(((int) getValueByFieldName(map, "modCount")), is(0));
        assertThat(map.size(), is(0));


        // After invoking the constructor, the class invariants must hold.
        assertClassInvariants(map);
    }

    /**
     * Test the exceptional behaviour of the constructor of {@link VerifiedIdentityHashMap} when
     * {@code null} is passed as a parameter.
     * <p/>
     * JML specification to check:
     * <pre>
     *   requires
     *     m == null;
     *   signals_only
     *     NullPointerException;
     *   signals
     *     (NullPointerException e) true;
     * </pre>
     */
    @Test
    public void testConstructorWithMapArgumentExceptionalBehaviour() {
        try {
            new VerifiedIdentityHashMap<>(null);
        } catch (NullPointerException e) {
            return;
        }
        fail("Expected a NullPointerException.");
    }

    /**
     * Checks the norman behaviour of the constructor of {@link VerifiedIdentityHashMap}
     * accepting a {@code Map} as an input parameter.
     * <p/>
     * JML specification to check:
     * <pre>
     *   requires
     *     m != null;
     *   ensures
     *     size == m.size() &&
     *     (\forall int i;
     *         0 <= i < table.length - 1;
     *         i % 2 == 0 ==> m.get(table[i]) == table[i+1]);
     * </pre>
     * <p/>
     * Obviously, the class invariants must hold after invoking the constructor. This
     * is also checked.
     *
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     * @throws InstantiationException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     * @throws NoSuchClassException
     */
    @Test
    public void testConstructorWithMapArgumentNormalBehaviour()
            throws InvocationTargetException, NoSuchMethodException, InstantiationException,
            IllegalAccessException, NoSuchFieldException, NoSuchClassException {
        final Map<String, String> paramMap = new HashMap<>();
        paramMap.put("aKey", "aValue");
        paramMap.put("anotherKey", "anotherValue");

        final VerifiedIdentityHashMap<String, String> map = new VerifiedIdentityHashMap<>(paramMap);

        // Check the size and the table content
        assertThat(map.size(), is(paramMap.size()));
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 0; i < table.length; i += 2) {
            assertThat(paramMap.get(table[i]), is(table[i + 1]));
        }

        // After invoking the constructor, the class invariants must hold.
        assertClassInvariants(map);
    }

}
