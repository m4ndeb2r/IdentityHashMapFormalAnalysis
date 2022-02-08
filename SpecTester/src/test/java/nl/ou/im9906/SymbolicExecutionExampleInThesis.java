package nl.ou.im9906;

import org.junit.Test;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.hamcrest.core.IsNot.not;

public class SymbolicExecutionExampleInThesis {

    @Test
    public void testF() {
        // a == 0 && b < 5 && c != 0 should give error
        f(1, 4, 1); // No error
        f(0, 5, 1); // No error
        f(0, 4, 0); // No error

        // f(0, -3, -1); // Error
        // f(0, 4, 1); // Error
    }

    private void f(int a, int b, int c) {
        int x = 0, y = 0, z = 0;
        if (a != 0) {
            x = -2;
        }
        if (b < 5) {
            if (a == 0 && c != 0) {
                y = 1;
            }
            z = 2;
        }
        assertThat(x + y + z, not(3));
    }

}
