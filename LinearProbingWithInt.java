/**
 * This implementation uses a linear probing as collision
 * resolution strategy. When associating a value with a key that is already in
 * the hash table, the convention is to replace the old value with the new value.
 */
public class LinearProbingHashWithInt {

	private static final int INIT_CAPACITY = 8;
	private static final int iNull = 0; //Integer.MIN_VALUE;

	private int pairs; 			// number of key-value pairs
	private int buckets; 		// size of linear probing table
	private int[] keys; 		// the keys
	private int[] vals; 		// the values

	/*@ // The hash table has at least one bucket.
	  @ instance invariant	buckets > 0;
	  @
	  @ //The arrays keys and vals are nonnull and are two different arrays.
	  @ instance invariant	keys != null && vals != null && keys != vals;
	  @
	  @ // The arrays keys and vals are equally long.
	  @ instance invariant	buckets == keys.length && buckets == vals.length;
	  @
	  @ //The hash table cant have a negative amount of elements.
	  @ //Currently doesn't work with delete, but the pairs 
	  @ //variable is important for resize.
	  @ //instance invariant	pairs == (\num_of int x; 0 <= x && x < buckets; keys[x] != iNull);
	  @
	  @ //Each key is at most ones in the hash table.
	  @ instance invariant	(\forall int y; 0 <= y && y < buckets && keys[y] != iNull;
	  @							(\forall int z; 0 <= z && z < buckets && keys[z] != iNull;
	  @								(keys[z] == keys[y]) ==> (z == y)));
	  @
	  @ //If a key is not null, then the value is also not null.
	  @ //	This is important for get(), since it returns null if the key is not in the table.
	  @ instance invariant	(\forall int x; 0 <= x && x < buckets;
	  @								(keys[x] != iNull) ==> (vals[x] != iNull));
	  @
	  @ instance invariant	(\forall int x; 0 <= x && x < buckets 
	  @							&& keys[x] != iNull && x >= hash(keys[x]);
	  @								(\forall int y; hash(keys[x]) <= y && y <= x;
	  @									keys[y] != iNull));
	  @
	  @ instance invariant	(\forall int x; 0 <= x && x < buckets 
	  @							&& keys[x] != iNull && x < hash(keys[x]);
	  @								(\forall int y; hash(keys[x]) <= y && y < buckets;
	  @									keys[y] != iNull)
	  @								&& (\forall int y; 0 <= y && y < x;
      @									keys[y] != iNull));
	  @
	  @ instance invariant	(\exists int x; 0 <= x && x < buckets; keys[x] == iNull);
	  @*/

    /**
     * Initializes an empty symbol table.
     */
    public LinearProbingHashWithInt() {
        this(INIT_CAPACITY);
    }

    /**
	 * Initializes an empty hash table with buckets buckets.
	 * 
	 * @param buckets
	 *            the initial number of buckets, is set to be at least 1.
	 */
    public LinearProbingHashWithInt(int buckets) {
		if (buckets < 1) buckets = 1;
		pairs = 0;
		this.buckets = buckets;
		keys = new int[buckets];
		vals = new int[buckets];
    }

    // hash function for keys - returns value between 0 and buckets-1
	/*@ public normal_behavior
	  @   requires	buckets > 0 && key != iNull;
	  @   ensures	(\forall int ho; (key == ho) ==> (\result == hash(ho)))
	  @				&& 0 <= \result && \result < buckets;
	  @   ensures_free	\result == hash(key);
	  @   assignable	\strictly_nothing;
	  @   accessible	this.buckets;
	  @
	  @ helper
	  @*/
	private /*@ strictly_pure @*/ int hash(int key) {
		return abs(key) % buckets;
	}

	//Returns the absolute value of the given number.
	//Unless the number is Integer.MIN_VALUE, then it return 0,
	//since in java there is no absolute value for this.
	/*@ helper */
	private int abs(int number) {
		if (number == Integer.MIN_VALUE) return 0;
		if (number < 0) return -number;
		return number;
	}

	//Returns the index of the given key, if the key is in the hash table.
	//	It starts its search from iHash which is the hash-value of the key.
	//  This is to essential to the hashtable concept.
	//	I originally used one loop with the modulo operator, but the 
	//	current two loop version is easier to verifiy.
	//Returns -1 if a null is found. If this is the case, then the key is
	//not in the hash table.
	/*@ public normal_behavior
	  @   requires	key != iNull;
	  @
	  @   //If the result is -1 the given key is not in the hash table.
	  @   ensures	(\result == -1) ==>
	  @					(\forall int x; 0 <= x && x < buckets; 
	  @						!(key == keys[x]));
	  @
	  @   //If the result is not -1 the given key is in the hash table 
	  @   //	and the result is the postion of the key.
	  @   ensures	(\result != -1) ==> 
	  @					(0 <= \result && \result < buckets
	  @					&& key == keys[\result]);
	  @*/
	private /*@ strictly_pure @*/ int getIndex(int key) {
		
		int iHash = hash(key);
		
		/*@ loop_invariant	iHash <= j && j <= buckets &&
		  @					(\forall int x; iHash <= x && x < j; 
		  @						!(key == keys[x]) && keys[x] != iNull);
		  @ assignable	\strictly_nothing;
		  @ decreases	buckets - j;
		  @*/
		for (int j = iHash; j < buckets; j++) {
			if (keys[j] == iNull) return -1;
			if (key == keys[j]) return j;
		}
		
		/*@ loop_invariant	0 <= k && k <= iHash &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @						!(key == keys[x]) && keys[x] != iNull);
		  @ assignable	\strictly_nothing;
		  @ decreases	iHash - k;
		  @*/
		for (int k = 0; k < iHash; k++) {
			if (keys[k] == iNull) return -1;
			if (key == keys[k]) return k;
		}
		
		//Should never be reached.
		
		return -1;
	}
	
	//Returns the index of an null-entry, if one is in the hash table.
	//	It starts its search from iHash which is the hash-value of a key.
	//  This is to essential to the hashtable concept.
	//	I originally used one loop with the modulo operator, but the 
	//	current two loop version is easier to verifiy.
	//Otherwise returns -1.
	/*@ public normal_behavior
	  @   requires	key != iNull;
	  @
	  @   //The result is always an index of the array and at this index
	  @   //is a null.
	  @   ensures	(0 <= \result && \result < buckets
	  @				&& keys[\result] == iNull);
	  @
	  @   //The following two ensures guarantee that this bucket is the 
	  @   //"nearest" null to the hash value of key.
	  @
	  @   ensures	(\result >= hash(key)) ==> 
	  @					(\forall int y; hash(key) <= y && y < \result;
	  @						keys[y] != iNull);
	  @
	  @   ensures	(\result < hash(key)) ==> 
	  @					((\forall int y; hash(key) <= y && y < buckets;
	  @						keys[y] != iNull)
	  @					&& (\forall int y; 0 <= y && y < \result;
      @						keys[y] != iNull));
	  @*/
	private /*@ strictly_pure @*/ int findEmpty(int key) {

		int iHash = hash(key);
		
		/*@ //Every postion in the array up until now is not null.
		  @ //	This is always true, since the method terminates if a null bucket is found.
		  @ loop_invariant	iHash <= j && j <= buckets &&
		  @					(\forall int x; iHash <= x && x < j; 
		  @						keys[x] != iNull);
		  @ assignable	\strictly_nothing;
		  @ decreases	buckets - j;
		  @*/
		for (int j = iHash; j < buckets; j++) {
			if (keys[j] == iNull) return j;
		}
		
		/*@ //Every postion in the array up until now is not null.
		  @ //	This is always true, since the method terminates if a null bucket is found.
		  @ loop_invariant	0 <= k && k <= iHash &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @						keys[x] != iNull);
		  @ assignable	\strictly_nothing;
		  @ decreases	iHash - k;
		  @*/
		for (int k = 0; k < iHash; k++) {
			if (keys[k] == iNull) {
				return k;
			}
		}
		
		//Should never be reached.
		return -1;
	}
	
	//Simply overwrites a key-value pair. This is a method, because it is difficult
	//to verifiy this part of the hash table, specifically the invariants.
	/*@ public normal_behavior
	  @   requires	key != iNull && val != iNull;
	  @   requires	(getIndex(key) == -1);
	  @   requires	(\exists int x; 0 <= x && x < buckets;
	  @					(\exists int y; 0 <= y && y < buckets && x != y; 
	  @						keys[y] == iNull && keys[x] == iNull));
	  @
	  @   //The key-value pair is now in the hash table and at the same position. 
	  @   ensures	key == keys[\result] && vals[\result] == val;
	  @
	  @   //The method has no effect on hash table positions were the key isn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < buckets && x != \result;
	  @					keys[x] == \old(keys[x]) && vals[x] == \old(vals[x]));
	  @
	  @   assignable	keys[*], vals[*], pairs;
	  @*/
	private int overwritePair(int key, int val) {
		int index = findEmpty(key);
		keys[index] = key;
		vals[index] = val;
		pairs++;
		return index;
	}

	/**
	 * Returns the value associated with the specified key in this hash table.
	 *
	 * @param key
	 *            the key
	 * @return the value associated with key in the hash table; 
	 *			null if no such value
	 * @throws IllegalArgumentException
	 *             if key is null
	 */
	/*@ public normal_behavior
	  @   requires	key != iNull;
	  @
	  @   //If the result is not null, the key is in keys
	  @   //	and the result is at the same postion in vals.
	  @   ensures	(\result != iNull) ==>
      @   				(\exists int y; 0 <= y && y < buckets;
	  @						key == keys[y] && vals[y] == \result);
	  @
	  @   //If the result is null, the key is not in keys.
	  @   ensures	(\result == iNull) ==> 
      @					(\forall int x; 0 <= x && x < buckets;
	  @						!(key == keys[x]));
	  @   
	  @   assignable	\strictly_nothing;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires	key == iNull;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
    public /*@ pure @*/ /*@ nullable @*/ int get(int key) {
		if (key == iNull) 
			throw new IllegalArgumentException("argument to get() is null");

		int index = getIndex(key);

		if (index != -1) return vals[index];

		return iNull;
	}
	
	
    /**
	 * Inserts the specified key-value pair into the hash table, overwriting the old
	 * value with the new value if the hash table already contains the specified key.
	 *
	 * @param key
	 *            the key
	 * @param val
	 *            the value
	 * @throws IllegalArgumentException
	 *             if key or val is null
	 */
	/*@ public normal_behavior
	  @   requires	key != iNull && val != iNull;
	  @
	  @   requires	(\exists int x; 0 <= x && x < buckets;
	  @					(\exists int y; 0 <= y && y < buckets && x != y; 
	  @						keys[y] == iNull && keys[x] == iNull));
	  @
	  @   //The key-value pair is now in the hash table and at the same position. 
	  @   ensures	key == keys[\result] && vals[\result] == val;
	  @
	  @   //The method has no effect on hash table positions were the key isn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < buckets && x != \result;
	  @					keys[x] == \old(keys[x]) && vals[x] == \old(vals[x]));
	  @
	  @   assignable	keys[*], vals[*], pairs;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires	key == iNull || val == iNull;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
    public int put(int key, int val) {
		if (key == iNull) throw new IllegalArgumentException("first argument to put() is iNull");
		if (val == iNull) throw new IllegalArgumentException("second argument to put() is iNull");

		int indexCopy = getIndex(key);
		
		if (indexCopy != -1) {
			vals[indexCopy] = val;
			return indexCopy;
		}
		
		return overwritePair(key, val);
    }

    /**
	 * Removes the specified key and its associated value from this hash table (if
	 * the key is in this hash table).
	 *
	 * @param key
	 *            the key
	 * @throws IllegalArgumentException
	 *             if key is null
	 */
	/*@ public normal_behavior
	  @   requires	key != iNull;
	  @
	  @   //The given key is not in the table. (This can already be true at the beginning)
	  @   ensures	(\forall int x; 0 <= x && x < buckets; keys[x] != key);
	  @
	  @   //The method has no effect on hash table positions were the key wasn't placed.
	  @   //ensures	(\forall int x; 0 <= x && x < buckets;
	  @		//			keys[x] == \old(keys[x]) && vals[x] == \old(vals[x]));
	  @
	  @   assignable keys[*], vals[*], pairs;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires key == iNull;
	  @   signals_only IllegalArgumentException;
	  @   signals (IllegalArgumentException e) true;
	  @*/
    public void delete(int key) {
		if (key == iNull)
			throw new IllegalArgumentException("argument to delete() is iNull");

		int index = getIndex(key);
		if (index == -1) return;
		
		int nextNull = findEmpty(key);
		
		if (index < nextNull) {
			/*@ loop_invariant	index <= i && i <= nextNull &&
			  @					(\forall int x; index <= x && x < i; 
			  @						keys[x] == iNull
			  @						&& vals[x] == iNull);
			  @ assignable	keys[*], vals[*];
			  @ decreases	nextNull - i;
			  @*/
			for (int i = index; i < nextNull; i++) {
				keys[i] = iNull;
				vals[i] = iNull;
			}
			return;
		}
		
		if (index > nextNull) {
			/*@ loop_invariant	index <= j && j <= buckets &&
			  @					(\forall int x; index <= x && x < j; 
			  @						keys[x] == iNull
			  @						&& vals[x] == iNull);
			  @ assignable	keys[*], vals[*];
			  @ decreases	buckets - j;
			  @*/
			for (int j = index; j < buckets; j++) {
				keys[j] = iNull;
				vals[j] = iNull;
			}
			
			/*@ loop_invariant	0 <= k && k <= nextNull &&
			  @					(\forall int x; 0 <= x && x < k; 
			  @						keys[x] == iNull
			  @						&& vals[x] == iNull);
			  @ assignable	keys[*], vals[*];
			  @ decreases	buckets - k;
			  @*/
			for (int k = 0; k < nextNull; k++) {
				keys[k] = iNull;
				vals[k] = iNull;
			}
		}
		
		
		//keys[index] = iNull;
		//vals[index] = iNull;
		//pairs--;
		
		//Problem: Now it is possible that the invariants don't hold.
    }
	
	/*@ public normal_behavior
	  @   requires	key != iNull;
	  @   requires	index == getIndex(key) && index != -1;
	  @   requires	nextNull == findEmpty(key);
	  @   requires	index < nextNull;
	  @
	  @   //The given key is not in the table.
	  @   ensures	(\forall int x; 0 <= x && x < buckets; keys[x] != key);
	  @
	  @   //The method has no effect on hash table positions were the key wasn't placed.
	  @   //ensures	(\forall int x; 0 <= x && x < buckets 
	  @		//			&& \old(keys[x]) != iNull && \old(keys[x]) != key;
	  @			//			getIndex(keys[x]) != -1));
	  @
	  @   assignable keys[*], vals[*];
	  @*/
    public void removeKey(int key, int index, int nextNull) {
		
		/*@ loop_invariant	index <= j && j <= (nextNull - 1) &&
		  @					(\forall int x; index <= x && x < j; 
		  @						keys[x] == \old(keys[x + 1])
		  @						&& vals[x] == \old(vals[x + 1]));
		  @ assignable	keys[*], vals[*];
		  @ decreases	nextNull - 1 - j;
		  @*/
		for (int j = index; j < nextNull - 1; j++) {
			keys[j] = keys[j + 1];
			vals[j] = vals[j + 1];
		}
		
		keys[nextNull - 1] = iNull;
		vals[nextNull - 1] = iNull;
    }
	
	/*@ public normal_behavior
	  @   requires	key != iNull;
	  @   requires	index == getIndex(key) && index != -1;
	  @   requires	nextNull == findEmpty(key);
	  @   requires	index < nextNull;
	  @
	  @   //The given key is not in the table.
	  @   //ensures	(\forall int x; 0 <= x && x < buckets; keys[x] != key);
	  @
	  @   //The method has no effect on hash table positions were the key wasn't placed.
	  @   //ensures	(\forall int x; 0 <= x && x < buckets 
	  @		//			&& \old(keys[x]) != iNull && \old(keys[x]) != key;
	  @			//			getIndex(keys[x]) != -1));
	  @
	  @   assignable keys[*], vals[*];
	  @*/
    public void removeKeys2(int key, int index, int nextNull) {
		
		/*@ loop_invariant	index <= i && i <= nextNull &&
		  @					(\forall int x; index <= x && x < i; 
		  @						keys[x] == iNull
		  @						&& vals[x] == iNull);
		  @ assignable	keys[index .. nextNull - 1], vals[index .. nextNull - 1];
		  @ decreases	nextNull - i;
		  @*/
		for (int i = index; i < nextNull; i++) {
			keys[i] = iNull;
			vals[i] = iNull;
		}
    }

	// resizes the hash table to the given capacity by re-hashing all of the keys
	/*@ public normal_behavior
	  @   requires	capacity >= buckets;
	  @   requires	(\exists int x; 0 <= x && x < buckets;
	  @					(\exists int y; 0 <= y && y < buckets && x != y; 
	  @						keys[y] == iNull && keys[x] == iNull));
	  @
	  @   ensures	(\forall int x; 0 <= x && x < \old(buckets) && \old(keys[x]) != iNull; 
	  @					(\exists int y; 0 <= y && y < buckets;
	  @						\old(keys[x]) == keys[y]));
	  @
	  @   assignable	keys, vals, buckets;
	  @*/
    private void resize(int capacity) {
        LinearProbingHashWithInt temp = new LinearProbingHashWithInt(capacity);
		
		/*@ loop_invariant	0 <= i && i <= buckets &&
		  @					(\forall int x; 0 <= x && x < i && keys[x] != iNull; 
		  @						(\exists int y; 0 <= y && y < capacity;
		  @							keys[x] == temp.keys[y]));
		  @ assignable	temp.keys[*], temp.vals[*], temp.pairs;
		  @ decreases	buckets - i;
		  @*/
        for (int i = 0; i < buckets; i++) {
            if (keys[i] != iNull) {
                temp.put(keys[i], vals[i]);
            }
        }
		
        keys = temp.keys;
        vals = temp.vals;
        buckets = temp.buckets;
    }
}