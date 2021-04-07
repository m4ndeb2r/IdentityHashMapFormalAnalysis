/**
 * This implementation uses a linear probing as collision
 * resolution strategy. When associating a value with a key that is already in
 * the hash table, the convention is to replace the old value with the new value.
 */
public class LinearProbingWithEquals {

	private static final int INIT_CAPACITY = 8;
	private static final HashObject keyDummy = new HashObject(Integer.MIN_VALUE);
		//If a key is deleted it is replaced with this. This is not a valid key.

	private int pairs; 									//number of key-value pairs
	private int buckets; 								//size of linear probing table
	private /*@ nullable @*/ HashObject[] keys; 		//the keys
	private /*@ nullable @*/ Object[] vals; 			//the values

	/*@ // The hash table has at least one bucket.
	  @ instance invariant	buckets > 0;
	  @
	  @ //The arrays keys and vals are nonnull and are two different arrays.
	  @ instance invariant	keys != null && vals != null && keys != vals;
	  @
	  @ // The arrays keys and vals are equally long.
	  @ instance invariant	buckets == keys.length && buckets == vals.length;
	  @
	  @ //pairs is the amount of key-value pairs in the hash table.
	  @ //Is important for resize which is currently not implemented.
	  @ //instance invariant	pairs == (\num_of int x; 0 <= x && x < buckets; keys[x] != null);
	  @
	  @ //The array vals is not a suptype.
	  @ instance invariant	\typeof(keys) == \type(HashObject[])
	  @						&& \typeof(vals) == \type(Object[]);
	  @
	  @ //Each key is at most ones in the hash table.
	  @ instance invariant	(\forall int y; 0 <= y && y < buckets 
	  @						&& keys[y] != null && !keyDummy.equals(keys[y]);
	  @							(\forall int z; y < z && z < buckets 
	  @							&& keys[z] != null && !keyDummy.equals(keys[z]);
	  @								!keys[z].equals(keys[y])));
	  @
	  @ //If a key is not null, then the value is also not null.
	  @ //	This is important for get(), since it returns null if the key is not in the table.
	  @ instance invariant	(\forall int x; 0 <= x && x < buckets;
	  @								(keys[x] != null) ==> (vals[x] != null));
	  @
	  @ //The following two invariants guarantee that between a key and it's hash value
	  @ //is no null value. This is important for LinearProbing so it can stop searching
	  @ //for a Keys if it finds a null.
	  @ instance invariant	(\forall int x; 0 <= x && x < buckets && x >= hash(keys[x])
	  @						&& keys[x] != null && !keyDummy.equals(keys[x]);
	  @							(\forall int y; hash(keys[x]) <= y && y <= x;
	  @								keys[y] != null));
	  @ instance invariant	(\forall int x; 0 <= x && x < buckets && x < hash(keys[x])
	  @						&& keys[x] != null && !keyDummy.equals(keys[x]);
	  @							(\forall int y; hash(keys[x]) <= y && y < buckets;
	  @								keys[y] != null)
	  @							&& (\forall int y; 0 <= y && y < x;
      @								keys[y] != null));
	  @
	  @ //At least one bucket contains a null. When the hash table is almost full,
	  @ //the resize() method is called to guarantee this.
	  @ //Note: the resize() method is currently not used.
	  @ instance invariant	(\exists int x; 0 <= x && x < buckets; keys[x] == null);
	  @*/

    /**
     * Initializes an empty symbol table.
     */
    public LinearProbingWithEquals() {
        this(INIT_CAPACITY);
    }

    /**
	 * Initializes an empty hash table with buckets buckets.
	 * 
	 * @param buckets
	 *            the initial number of buckets, is set to be at least 1.
	 */
	/*@ public normal_behavior
	  @   requires	buckets > 0;
	  @
	  @   ensures	\fresh(keys) && \fresh(vals)
	  @				&& this.buckets == buckets && pairs == 0;
	  @
	  @   assignable	pairs, buckets, keys, vals;
	  @*/
    public LinearProbingWithEquals(int buckets) {
		if (buckets < 1) buckets = 1;
		pairs = 0;
		this.buckets = buckets;
		keys = new HashObject[buckets];
		vals = new Object[buckets];
    }

    // hash function for keys - returns value between 0 and buckets-1
	/*@ public normal_behavior
	  @   requires	buckets > 0 && !keyDummy.equals(key);
	  @   ensures	(\forall HashObject ho; key.equals(ho) 
	  @					==> (\result == hash(ho)))
	  @				&& 0 <= \result && \result < buckets;
	  @   ensures_free	\result == hash(key);
	  @   assignable	\strictly_nothing;
	  @   accessible	key.value, this.buckets;
	  @
	  @ helper
	  @*/
	private /*@ strictly_pure @*/ int hash(HashObject key) {
		return abs(key.hashCode()) % buckets;
	}

	//Returns the absolute value of the given number.
	//Unless the number is Integer.MIN_VALUE, then it return 0,
	//since in java there is no absolute value for this.
	/*@ helper*/
	private int abs(int number) {
		if (number == Integer.MIN_VALUE) return 0;
		if (number < 0) return -number;
		return number;
	}
	
	//Returns the index of the given key, if the key is in the hash table.
	//	It starts its search from the hash-value of the key.
	//  This is to essential to the hashtable concept.
	//	I originally used one loop with the modulo operator, but the 
	//	current two loop version is easier to verifiy.
	//Returns -1 if a null is found. If this is the case, then the key is
	//not in the hash table.
	/*@ public normal_behavior
	  @   requires	!keyDummy.equals(key);
	  @
	  @   //If the result is -1 the given key is not in the hash table.
	  @   ensures	(\result == -1) ==>
	  @					(\forall int x; 0 <= x && x < buckets; 
	  @						!(key.equals(keys[x])));
	  @
	  @   //If the result is not -1 the given key is in the hash table 
	  @   //	and the result is the postion of the key.
	  @   ensures	(\result != -1) ==> 
	  @					(0 <= \result && \result < buckets
	  @					&& key.equals(keys[\result]));
	  @*/
	private /*@ strictly_pure @*/ int getIndex(HashObject key) {
		
		int iHash = hash(key);
		
		/*@ //Every postion in the array up until now is not null and not the given key.
		  @ //	This is always true, since the method terminates if a null bucket
		  @ //  or a bucket with the key is found.
		  @ loop_invariant	iHash <= j && j <= buckets &&
		  @					(\forall int x; iHash <= x && x < j; 
		  @						!(key.equals(keys[x])) && keys[x] != null);
		  @ assignable	\strictly_nothing;
		  @ decreases	buckets - j;
		  @*/
		for (int j = iHash; j < buckets; j++) {
			if (keys[j] == null) return -1;
			if (key.equals(keys[j])) return j;
		}
		
		/*@ //Every postion in the array up until now is not null and not the given key.
		  @ //	This is always true, since the method terminates if a null bucket
		  @ //  or a bucket with the key is found.
		  @ loop_invariant	0 <= k && k <= iHash &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @						!(key.equals(keys[x])) && keys[x] != null);
		  @ assignable	\strictly_nothing;
		  @ decreases	iHash - k;
		  @*/
		for (int k = 0; k < iHash; k++) {
			if (keys[k] == null) return -1;
			if (key.equals(keys[k])) return k;
		}
		
		//Should never be reached.
		return -1;
	}
	
	//Returns the index of an null-entry and there is always at least one.
	//	It starts its search from the hash-value of a key.
	//  This is to essential to the hashtable concept.
	//	I originally used one loop with the modulo operator, but the 
	//	current two loop version is easier to verifiy.
	//Never returns -1.
	/*@ public normal_behavior
	  @   requires	!keyDummy.equals(key);
	  @
	  @   //The result is always an index of the array and at this index
	  @   //is a null.
	  @   ensures	0 <= \result && \result < buckets
	  @				&& keys[\result] == null;
	  @
	  @   //The following two ensures guarantee that the resulting index
	  @   // is the "nearest" null to the hash value of key.
	  @   ensures	(\result >= hash(key)) ==> 
	  @					(\forall int y; hash(key) <= y && y < \result;
	  @						keys[y] != null);
	  @   ensures	(\result < hash(key)) ==> 
	  @					((\forall int y; hash(key) <= y && y < buckets;
	  @						keys[y] != null)
	  @					&& (\forall int y; 0 <= y && y < \result;
      @						keys[y] != null));
	  @*/
	private /*@ strictly_pure @*/ int findEmpty(HashObject key) {

		int iHash = hash(key);
		
		/*@ //Every postion in the array up until now is not null.
		  @ //	This is always true, since the method terminates if a null bucket is found.
		  @ loop_invariant	iHash <= j && j <= buckets &&
		  @					(\forall int x; iHash <= x && x < j; 
		  @						keys[x] != null);
		  @ assignable	\strictly_nothing;
		  @ decreases	buckets - j;
		  @*/
		for (int j = iHash; j < buckets; j++) {
			if (keys[j] == null) return j;
		}
		
		/*@ //Every postion in the array up until now is not null.
		  @ //	This is always true, since the method terminates if a null bucket is found.
		  @ loop_invariant	0 <= k && k <= iHash &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @						keys[x] != null);
		  @ assignable	\strictly_nothing;
		  @ decreases	iHash - k;
		  @*/
		for (int k = 0; k < iHash; k++) {
			if (keys[k] == null) return k;
		}
		
		//Should never be reached.
		return -1;
	}
	
	//Overwrites a key-value pair. This is a method, because it is difficult
	//to verifiy this part of the hash table, specifically the invariants.
	/*@ public normal_behavior
	  @   requires	!keyDummy.equals(key);
	  @
	  @   //The key is not in the hash table.
	  @   requires	getIndex(key) == -1;
	  @   
	  @   //There are at least two nulls in the hash table.
	  @   //So the invarants hold after a null is replaced with a key.
	  @   requires	(\exists int x; 0 <= x && x < buckets;
	  @					(\exists int y; x < y && y < buckets; 
	  @						keys[y] == null && keys[x] == null));
	  @
	  @   //The key-value pair is now in the hash table and at the same position.
	  @   ensures	(\exists int x; 0 <= x && x < buckets;
	  @					key.equals(keys[x]) && vals[x] == val);
	  @
	  @   //The method has no effect on hash table positions were the key isn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < buckets && x != \result;
	  @					keys[x] == \old(keys[x]) && vals[x] == \old(vals[x]));
	  @
	  @   assignable	keys[*], vals[*], pairs;
	  @*/
	private int overwritePair(HashObject key, Object val) {
		int index = findEmpty(key);
		keys[index] = key;
		vals[index] = val;
		pairs++;
		return index;
	}

	/**
	 * Returns the value associated with the given key in this hash table.
	 *
	 * @param key
	 *            the key
	 * @return the value associated with key in the hash table; 
	 *			null if no such value
	 * @throws IllegalArgumentException
	 *             if key is null
	 */
	/*@ public normal_behavior
	  @   requires	!keyDummy.equals(key);
	  @
	  @   //If the result is not null, the key is in keys
	  @   //	and the result is at the same postion in vals.
	  @   ensures	(\result != null) ==>
      @   				(\exists int y; 0 <= y && y < buckets;
	  @						key.equals(keys[y]) && vals[y] == \result);
	  @
	  @   //If the result is null, the key is not in keys.
	  @   ensures	(\result == null) ==> 
      @					(\forall int x; 0 <= x && x < buckets;
	  @						!(key.equals(keys[x])));
	  @   
	  @   //We can't make the whole method strictly pure, 
	  @   //because an exception creates an object.
	  @   assignable	\strictly_nothing;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires	key == null || keyDummy.equals(key);
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
    public /*@ pure @*/ /*@ nullable @*/ Object get(HashObject key) {
		if (key == null || keyDummy.equals(key)) 
			throw new IllegalArgumentException("The argument to get() is invalid");

		int index = getIndex(key);
		
		if (index != -1) return vals[index];
		
		return null;
	}

    /**
	 * Inserts the given key-value pair into the hash table, overwriting the old
	 * value with the new value if the hash table already contains the given key.
	 *
	 * @param key
	 *            the key
	 * @param val
	 *            the value
	 * @throws IllegalArgumentException
	 *             if key or val is null
	 */
	/*@ public normal_behavior
	  @   requires	!keyDummy.equals(key);
	  @   
	  @   //There are at least two nulls in the hash table.
	  @   //So the invarants hold after a null is replaced with a key.
	  @   requires	(\exists int x; 0 <= x && x < buckets;
	  @					(\exists int y; x < y && y < buckets; 
	  @						keys[y] == null && keys[x] == null));
	  @
	  @   //The key-value pair is now in the hash table and at the same position.
	  @   ensures	(\exists int x; 0 <= x && x < buckets;
	  @					key.equals(keys[x]) && vals[x] == val);
	  @
	  @   //The method has no effect on hash table positions were the key isn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < buckets && x != \result;
	  @					keys[x] == \old(keys[x]) && vals[x] == \old(vals[x]));
	  @
	  @   assignable	keys[*], vals[*], pairs;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires	key == null || keyDummy.equals(key) || val == null;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
    public int put(HashObject key, Object val) {
		if (key == null || keyDummy.equals(key)) 
			throw new IllegalArgumentException("The first argument to put() is invalid");
		if (val == null) 
			throw new IllegalArgumentException("The second argument to put() is invalid");

		int index = getIndex(key);
		
		if (index != -1) {
			vals[index] = val;
			return index;
		}

		return overwritePair(key, val);
    }

    /**
	 * Removes the given key from this hash table and therefore its 
	 * associated value inaccessible (if the key is in this hash table).
	 *
	 * @param key
	 *            the key
	 * @throws IllegalArgumentException
	 *             if key is null
	 */
	/*@ public normal_behavior
	  @   requires	!keyDummy.equals(key);
	  @
	  @   //The given key is not in the table. (This can already be true at the beginning)
	  @   ensures	(\forall int x; 0 <= x && x < buckets; !key.equals(keys[x]));
	  @
	  @   //The method has no effect on hash table positions were the key wasn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < buckets && x != \result;
	  @					keys[x] == \old(keys[x]) && vals[x] == \old(vals[x]));
	  @
	  @   assignable keys[*], pairs;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires key == null || keyDummy.equals(key);
	  @   signals_only IllegalArgumentException;
	  @   signals (IllegalArgumentException e) true;
	  @*/
    public int delete(HashObject key) {
		if (key == null || keyDummy.equals(key)) 
			throw new IllegalArgumentException("The argument to delete() is invalid");

		int index = getIndex(key);
		if (index == -1) return index;
		
		keys[index] = keyDummy;
		pairs--;
		
		return index;
    }
}