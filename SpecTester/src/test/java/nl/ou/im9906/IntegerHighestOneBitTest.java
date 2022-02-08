package nl.ou.im9906;

import org.junit.Test;

import static nl.ou.im9906.ReflectionUtils.isPowerOfTwo;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThan;
import static org.hamcrest.Matchers.lessThanOrEqualTo;
import static org.hamcrest.core.Is.is;

public class IntegerHighestOneBitTest {

    /**
     * Test if the following JML holds:
     *    requires param0 > 0;
     *    ensures
     *      \result <= param0 &&
     *      (\bigint)2 * \result > param0;
     *    ensures
     *      (\exists \bigint i;
     *        0 <= i < \result;
     *        \dl_pow(2,i) == \result); // result is a power of two
     *
     */
    @Test
    public void testIntegerHighestOneBit() {
        for (int i = 1; i < Integer.MAX_VALUE / 2; i *= 3) {
            final int highestOneBit = Integer.highestOneBit(i);
            assertThat(highestOneBit, lessThanOrEqualTo(i));
            assertThat((long)highestOneBit * 2L, greaterThan((long)i));
            assertThat(isPowerOfTwo(highestOneBit), is(true));
        }
    }
}
