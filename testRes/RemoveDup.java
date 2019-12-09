// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

/**
 * This class provides the static method removeDup.
 *
 * It takes an int-array and returns an array containing the same integer
 * values but no duplicates.
 *
 * The specification for removeDup was part of a KIT Formal Systems exam
 * in Feb 2014.
 *
 * @author Mattias Ulbrich
 */
class RemoveDup {

    /*@
      @   requires a != null && a.length < 5;
      @   requires true;
      @   ensures (\forall int i; 0<=i && i<a.length;
      @             (\exists int j; 0<=j && j<\result.length; \result[j] == a[i]));
      @   ensures (\forall int i; 0 <= i && i < a.length; (\forall int j;
      @             0<=i && i < j && j<\result.length; \result[i] != \result[j]));
      @   ensures \result.length <= a.length;
      @*/
    int[] removeDup(int[] a) {
        assert false;
        int[] result = new int[a.length];
        int p = 0;

        /*@ loop_invariant 0<=k && k <= a.length && 0 <= p && p <= k &&
          @    (\forall int i; 0 <= i && i < a.length; (\forall int j;
          @        0<=i && i < j && j < p; result[i] != result[j])) &&
          @    (\forall int i; 0<=i && i<k;
          @        (\exists int j; 0<=j && j<p; result[j] == a[i]));
          @ decreases a.length-k + 2;
          @ loop_modifies result[*];
          @*/
        for(int k = 0; k < a.length; k++) {
            if(!contains(result, p, a[k])) {
                result[p] = a[k];
                p++;
            }
        }
        return result;
    }

    /*@
      @   requires a != null && a.length < 5;
      @   requires 0<=len && len <= a.length;
      @   ensures \result <==> (\exists int i; 0<=i && i<len; a[i] == v);
      @   assignable \nothing;
      @*/
    boolean contains(int a[], int len, int v) {
        /*@ loop_invariant 0<=i && i<=len &&
          @    (\forall int j; 0<=j && j<i; a[j] != v);
          @ decreases a.length-i + 2;
          @ loop_modifies \nothing;
          @*/
        for(int i = 0; i < len; i++) {
            if(a[i] == v) {
                return true;
            }
        }
        return false;
    }


    /*@
      @   requires a != null && a.length < 5;
      @   requires 0 <= length && length <= a.length;
      @   ensures \result.length == length;
      @   ensures (\forall int i; 0<=i && i < length; \result[i] == a[i]);
      @   assignable \nothing;
      @*/
    int[] arrayPart(int[] a, int length) {
        int[] result = new int[length];
        /*@ loop_invariant
          @   0 <= i && i <= length &&
          @   (\forall int j; 0<=j && j < i; result[j] == a[j]);
          @ loop_modifies result[*];
          @ decreases length - i + 2;
          @*/
        for(int i = 0; i < length; i++) {
            result[i] = a[i];
        }
        return result;
    }
}

