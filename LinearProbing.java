/**
 * This implementation uses a linear probing as collision
 * resolution strategy. When associating a value with a key that is already in
 * the hash table, the convention is to replace the old value with the new value.
 */
public class LinearProbingHash {
	
	//Note: In the orginal Version, after a delete() call, all Key-Value pairs
	//got relocated, so between two key with the same hashvalue is now no null 
	//entry. While this is more efficent, it also makes the specification and 
	//verification harder. And it also needed the resize() methode. 
	//So for now I don't use it.

	private static final int INIT_CAPACITY = 8;

	private int pairs; 									// number of key-value pairs
	private int buckets; 								// size of linear probing table
	private /*@ nullable @*/ HashObject[] keys; 		// the keys
	private /*@ nullable @*/ Object[] vals; 			// the values

	/*@ // The hash table has at least one bucket.
	  @ instance invariant	buckets > 0;
	  @
	  @ //The arrays keys and vals are nonnull and are two different arrays.
	  @ instance invariant	keys != null && vals != null && keys != vals;
	  @
	  @ //The arrays keys and vals are not suptypes.
	  @ //It limits vals a bit, but helps verification.
	  @ //Maybe not important for linear probing.
	  @ instance invariant	\typeof(keys) == \type(HashObject[]) 
	  @						&& \typeof(vals) == \type(Object[]);
	  @
	  @ // The arrays keys and vals are equally long.
	  @ instance invariant	buckets == keys.length && buckets == vals.length;
	  @
	  @ //The hash table cant have a negative amount of elements.
	  @ //Doesn't work at the moment.
	  @ //instance invariant	pairs == (\num_of int x; 0 <= x && x < buckets; keys[x] != null);
	  @
	  @
	  @ //Each key is at most ones in the hash table.
	  @ instance invariant	(\forall int y; 0 <= y && y < buckets && keys[y] != null;
	  @							(\forall int z; 0 < z && z < buckets && keys[z] != null;
	  @								keys[z].equals(keys[y]) ==> (z == y)));
	  @
	  @ //If a key is not null, then the value is also not null.
	  @ //	This is important for get(), since it returns null if the key is not in the table.
	  @ instance invariant	(\forall int x; 0 <= x && x < buckets;
	  @								(keys[x] != null) ==> (vals[x] != null));
	  @*/

    /**
     * Initializes an empty symbol table.
     */
    public LinearProbingHash() {
        this(INIT_CAPACITY);
    }

    /**
	 * Initializes an empty hash table with buckets buckets.
	 * 
	 * @param buckets
	 *            the initial number of buckets, is set to be at least 1.
	 */
    public LinearProbingHash(int buckets) {
		if (buckets < 1)
			buckets = 1;
		pairs = 0;
		this.buckets = buckets;
		keys = new HashObject[buckets];
		vals = new Object[buckets];
    }

    // hash function for keys - returns value between 0 and buckets-1
	/*@ public normal_behavior
	  @   requires	buckets > 0;
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
		if (number == Integer.MIN_VALUE)
			return 0;
		if (number < 0)
			return -number;
		return number;
	}

	//Returns the index of the given key, if the key is in the hash table.
	//	It starts its search from iHash which is the hash-value of the key.
	//  This is to essential to the hashtable concept.
	//	I originally used one loop with the modulo operator, but the 
	//	current two loop version is easier to verifiy.
	//Otherwise returns -1.
	/*@ public normal_behavior
	  @   requires 	0 <= iHash && iHash < buckets;
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
	private /*@ strictly_pure @*/ int getIndex(int iHash, HashObject key) {
		/*@ //Every postion in the array up until now didnt include the key.
		  @ //	This is always true, since the method terminates if the key is found.
		  @ loop_invariant	iHash <= j && j <= buckets &&
		  @					(\forall int x; iHash <= x && x < j; 
		  @						!(key.equals(keys[x])));
		  @ assignable	\strictly_nothing;
		  @ decreases	buckets - j;
		  @*/
		for (int j = iHash; j < buckets; j++) {
			if (key.equals(keys[j])) {
				return j;
			}
		}
		
		/*@ //Every postion in the array up until now didnt include the key.
		  @ //	This is always true, since the method terminates if the key is found.
		  @ loop_invariant	0 <= k && k <= iHash &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @						!(key.equals(keys[x])));
		  @ assignable	\strictly_nothing;
		  @ decreases	iHash - k;
		  @*/
		for (int k = 0; k < iHash; k++) {
			if (key.equals(keys[k])) {
				return k;
			}
		}
		
		return -1;
	}
	
	//Returns the index of an null-entry, if one is in the hash table.
	//	It starts its search from iHash which is the hash-value of a key.
	//  This is to essential to the hashtable concept.
	//	I originally used one loop with the modulo operator, but the 
	//	current two loop version is easier to verifiy.
	//Otherwise returns -1.
	/*@ public normal_behavior
	  @   requires 	0 <= iHash && iHash < buckets;
	  @
	  @   //If the result is -1, no bucket in keys is null.
	  @   ensures	(\result == -1) ==>
	  @					(\forall int x; 0 <= x && x < buckets; 
	  @						keys[x] != null);
	  @
	  @   //If the result is not -1, at least one bucket in keys is null
	  @   //	and the result is postion of this bucket.
	  @   //It is no guarantee that this bucket is the "nearest" to iHash.
	  @   ensures	(\result != -1) ==> 
	  @					(0 <= \result && \result < buckets
	  @					&& keys[\result] == null);
	  @*/
	private /*@ strictly_pure @*/ int findEmpty(int iHash) {		
		/*@ //Every postion in the array up until now is not null.
		  @ //	This is always true, since the method terminates if a null bucket is found.
		  @ loop_invariant	iHash <= j && j <= buckets &&
		  @					(\forall int x; iHash <= x && x < j; 
		  @						keys[x] != null);
		  @ assignable	\strictly_nothing;
		  @ decreases	buckets - j;
		  @*/
		for (int j = iHash; j < buckets; j++) {
			if (keys[j] == null) {
				return j;
			}
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
			if (keys[k] == null) {
				return k;
			}
		}
		
		return -1;
	}
	
	//Simply overwrites a key-value pair. This is a method, because it is difficult
	//to verifiy this part of the hash table, specifically the invariants.
	/*@ public normal_behavior
	  @   requires	0 <= index && index < buckets;
	  @   requires	(getIndex(index, key) == -1);
	  @
	  @   ensures	keys[index] == key && vals[index] == val;
	  @
	  @   assignable	keys[index], vals[index];
	  @*/
	private void overwritePair(HashObject key, Object val, int index) {
		keys[index] = key;
		vals[index] = val;
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
	  @   assignable	\strictly_nothing;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires	key == null;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
    public /*@ pure @*/ /*@ nullable @*/ Object get(HashObject key) {
		if (key == null)
			throw new IllegalArgumentException("argument to get() is null");

		int index = getIndex(hash(key), key);

		if (index != -1) {
			return vals[index];
		}

		return null;
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
	  @   //The key-value pair is now in the hash table and at the same position. 
	  @   ensures	(\exists int x; 0 <= x && x < buckets;
	  @					key.equals(keys[x]) && vals[x] == val);   
	  @
	  @   //The method has no effect on hash table positions were the key isn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < buckets && !key.equals(keys[x]);
	  @					keys[x] == \old(keys[x]) && vals[x] == \old(vals[x]));
	  @
	  @   assignable	keys[*], vals[*], pairs;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires	key == null || val == null;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
    public void put(HashObject key, Object val) {
		if (key == null) throw new IllegalArgumentException("first argument to put() is null");
		if (val == null) throw new IllegalArgumentException("second argument to put() is null");

		int iHash = hash(key);
		int indexCopy = getIndex(iHash, key);
		
		if (indexCopy != -1) {
			vals[indexCopy] = val;
			return;
		}
		
		int indexNull = findEmpty(iHash);
		
		if (indexNull != -1) {
			overwritePair(key, val, indexNull);
			pairs++;
			return;
		}
		
		//Without resize we can't guarantee an empty bucket.
		overwritePair(key, val, iHash);
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
	  @   //The given key is not in the table. (This can already be true at the beginning)
	  @   ensures	(\forall int x; 0 <= x && x < buckets;
	  @					!(key.equals(keys[x])));
	  @
	  @   //The method has no effect on hash table positions were the key wasn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < buckets && \old(!key.equals(keys[x]));
	  @					keys[x] == \old(keys[x]) && vals[x] == \old(vals[x]));
	  @
	  @   assignable keys[*], vals[*], pairs;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires key == null;
	  @   signals_only IllegalArgumentException;
	  @   signals (IllegalArgumentException e) true;
	  @*/
    public void delete(HashObject key) {
		if (key == null)
			throw new IllegalArgumentException("argument to delete() is null");

		int index = getIndex(hash(key), key);
		
		if (index != -1) {
			keys[index] = null;
			vals[index] = null;
			pairs--;
		}
    }
}