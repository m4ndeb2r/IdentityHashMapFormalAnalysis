package nl.ou.im9906;

import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.ReflectionUtils.getValueByStaticFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.junit.Assert.fail;

/**
 * Because the {@link VerifiedIdentityHashMap} can grow very big, some unit tests pushing the
 * class to its limits run into memory errors. Therefore we use a {@link SmallIdentityHashMap} to
 * simulate a small version of the {@link VerifiedIdentityHashMap} to enable testing the limits.
 * This test class focusses on the constructors.
 */
public class SmallIdentityHashMapConstructorTest {

    /**
     * Tests the exceptional_behavior case when the capacity is exhausted.
     *
     * The JML specification to test:
     * <pre>
     *   public exceptional_behavior
     *     requires
     *       MAXIMUM_CAPACITY == 536870912 &&
     *       m.size() > MAXIMUM_CAPACITY - 1;
     *     signals_only
     *       IllegalStateException;
     *     signals
     *       (IllegalStateException e) true;
     * </pre>
     *
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     * @throws InvocationTargetException
     */
    @Test
    public void testConstructorWithTooBigMapAsArgument()
            throws IllegalAccessException, NoSuchMethodException,
            InvocationTargetException, NoSuchFieldException {

        final Object value = new Object();
        final Map<Integer, Object> paramMap = new HashMap<>();
        final int max = ((int)getValueByStaticFieldName(SmallIdentityHashMap.class, "MAXIMUM_CAPACITY"));
        for (int i = 0; i < max; i++) {
            paramMap.put(i, value);
        }
        try {
            new SmallIdentityHashMap<>(paramMap);
            fail("Expected an IllegalStateException (capacity exhausted).");
        } catch (IllegalStateException e) {
            assertThat(e.getMessage(), is("Capacity exhausted."));
        }
    }

    /**
     * Tests the limits of the normal_behavior case when the capacity
     * is almost exhausted, but not quite.
     *
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     * @throws InvocationTargetException
     */
    @Test
    public void testConstructorWithMapThatAlmostFillsTheTableAsArgument()
            throws
            IllegalAccessException, NoSuchMethodException,
            InvocationTargetException, NoSuchFieldException,
            NoSuchClassException {

        final Object value = new Object();
        final Map<Integer, Object> paramMap = new HashMap<>();
        final int limit = ((int)getValueByStaticFieldName(SmallIdentityHashMap.class, "MAXIMUM_CAPACITY")) - 1;
        for (int i = 0; i < limit; i++) {
            paramMap.put(i, value);
        }
        final SmallIdentityHashMap<Integer, Object> smallMap = new SmallIdentityHashMap<>(paramMap);
        assertClassInvariants(smallMap);
    }

}
