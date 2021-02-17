/**
 * This implementation uses a linear probing as collision
 * resolution strategy. When associating a value with a key that is already in
 * the hash table, the convention is to replace the old value with the new value.
 */
public class LinearProbingHash {

	private static final int INIT_CAPACITY = 8;

	private int pairs; 				// number of key-value pairs
	private int buckets; 			// size of linear probing table
	private HashObject[] keys; 		// the keys
	private Object[] vals; 			// the values

	/*@ // The hash table has at least one chain.
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
	  @ instance invariant	buckets == vals.length && buckets == keys.length;
	  @
	  @ //The hash table cant have a negative amount of elements.
	  @ //instance invariant	pairs == (\num_of int x; 0 <= x && x < keys.length; keys[x] != null);
	  @ //instance invariant	0 <= pairs && pairs < buckets;
	  @
	  @ //Each key is at most ones in the hash table.
	  @ instance invariant	(\forall int y; 0 <= y && y < keys.length && keys[y] != null;
	  @							(\forall int z; 0 < z && z < keys.length && keys[z] != null;
	  @								keys[z].equals(keys[y]) ==> (z == y)));
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
	  @   ensures	(\forall HashObject o; key.equals(o) 
	  @					==> (\result == hash(o)))
	  @				&& 0 <= \result && \result < buckets;
	  @   ensures_free	\result == hash(key);
	  @   assignable	\strictly_nothing;
	  @   accessible	key.value, this.buckets;
	  @*/
	private /*@ strictly_pure @*/ int /*@ helper*/ hash(HashObject key) {
		//return (key.hashCode() * key.hashCode()) % buckets;
		return abs(key.hashCode()) % buckets;
		//return ((key.hashCode() % buckets) + buckets) % buckets;
	}

	//Returns the absolute value of the given number.
	//Unless the number is Integer.MIN_VALUE, then it return 0,
	//since in java there is no absolute value for this.
	private int /*@ helper*/ abs(int number) {
		if (number == Integer.MIN_VALUE)
			return 0;
		if (number < 0)
			return -number;
		return number;
	}

	/*@ public normal_behavior
	  @   requires 	0 <= iHash && iHash < buckets && \invariant_for(this);
	  @		//Is key still nonnull if the method is a helper?
	  @
	  @   //If the result is -1 the given key is not in the hash table.
	  @   ensures	(\result == -1) ==>
	  @					(\forall int x; 0 <= x && x < buckets; 
	  @						!(key.equals(keys[(x + iHash) % buckets])));
	  @
	  @   //If the result is not -1 the given key is in the hash table 
	  @   //	and the result is the postion of the key.
	  @   ensures	(\result != -1) ==> 
	  @					(0 <= \result && \result < buckets
	  @					&& key.equals(keys[\result]));
	  @*/
	private /*@ strictly_pure @*/ int /*@ helper*/ getIndex(int iHash, HashObject key) {
		//Note: In the orginal Version, after a delete() call, all Key-Value pairs
		//got relocated, so between two key with the same hashvalue is now null 
		//entry. While this is more efficent, it also makes the specification and 
		//verification harder. So for now I don't use it.
		
		int index;
		
		/*@ //Every postion in the array up until now didnt include the key.
		  @ //	This is always true, since the method terminates if the key is found.
		  @ loop_invariant	0 <= j && j <= keys.length &&
		  @					(\forall int x; 0 <= x && x < j; 
		  @						!(key.equals(keys[(x + iHash) % buckets])));
		  @ assignable	\strictly_nothing;
		  @ decreases	keys.length - j;
		  @*/
		for (int j = 0; j < keys.length; j++) {
			index = (j + iHash) % buckets;
			if (key.equals(keys[index])) {
				return index;
			}
		}
		
		return -1;
	}
	
	/*@ public normal_behavior
	  @   requires 	0 <= iHash && iHash < buckets && \invariant_for(this);
	  @
	  @   //If the result is -1, no bucket in keys is null.
	  @   ensures	(\result == -1) ==>
	  @					(\forall int x; 0 <= x && x < keys.length; 
	  @						keys[(x + iHash) % buckets] != null);
	  @
	  @   //If the result is not -1, at least one bucket in keys is null
	  @   //	and the result is postion of this bucket.
	  @   //It is no guarantee that this bucket is the "nearest" to iHash.
	  @   ensures	(\result != -1) ==> 
	  @					(0 <= \result && \result < buckets
	  @					&& keys[\result] == null);
	  @					//&& (iHash <= \result) ==> (\forall int x; iHash <= x && x < \result;
	  @						//						keys[x] != null)
	  @					//&& (iHash > \result) ==> ((\forall int x; iHash <= x && x < buckets;
	  @						//						keys[x] != null)
	  @							//				 && (\forall int x; 0 <= x && x < \result;
	  @								//				keys[x] != null)));
	  @*/
	private /*@ strictly_pure @*/ int /*@ helper*/ findEmpty(int iHash) {
		int index;
		
		/*@ //Every postion in the array up until now is not null.
		  @ //	This is always true, since the method terminates if a null bucket is found.
		  @ loop_invariant	0 <= j && j <= keys.length &&
		  @					(\forall int x; 0 <= x && x < j; 
		  @						keys[(x + iHash) % buckets] != null);
		  @ assignable	\strictly_nothing;
		  @ decreases	keys.length - j;
		  @*/
		for (int j = 0; j < keys.length; j++) {
			index = (j + iHash) % buckets;
			if (keys[index] == null) {
				return index;
			}
		}
		
		return -1;
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
	  @   requires	\invariant_for(this);
	  @
	  @   //If the result is not null, the key is in keys
	  @   //	and the result is at the same postion in vals.
	  @   ensures	(\result != null) ==>
      @   				(\exists int y; 0 <= y && y < keys.length;
	  @						key.equals(keys[y]) && vals[y] == \result);
	  @
	  @   //If the result is null, the key is not in keys.
	  @   ensures	(\result == null) ==> 
      @					(\forall int y; 0 <= y && y < keys.length;
	  @						!(key.equals(keys[(y + hash(key)) % buckets])));
	  @   
	  @   assignable	\strictly_nothing;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires	key == null;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
    public /*@ pure @*/ /*@ nullable @*/ Object /*@ helper*/ get(HashObject key) {
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
	  @   requires	true;
	  @   
	  @   //The amount of elements in the hash table (called pairs) is now either pairs or pairs+1.
	  @   ensures	(pairs == \old(pairs)) || (pairs == \old(pairs) + 1);
	  @   
	  @   //If pairs is now pairs, then the key was and still is in the table and 
	  @   //	the given value is at this postion OR position hash(key) got overwriten.
	  @   //	The current contract might not hold if resize is used, 
	  @   //	since the contract requires that the keys postion did not change.
	  @   ensures	(\exists int x; 0 <= x && x < keys.length;
	  @						\old(key.equals(keys[x])) ==> (key.equals(keys[x]) && vals[x] == val));
	  @
	  @   ensures	(\forall int x; 0 <= x && x < keys.length; 
	  @					!\old(key.equals(keys[x])))
	  @				==> (keys[hash(key)] == key && vals[hash(key)] == val);
	  @   
	  @   //If pairs is now pairs+1, then there was a bucket in keys and vals that was null
	  @   //	and is now key and val.
	  @   //It is no guarantee that this bucket is the "nearest" to hash(key).
	  @   ensures	(pairs == \old(pairs) + 1) ==>
	  @					(\exists int x; 0 <= x && x < keys.length;
	  @						key.equals(keys[x]) && \old(keys[x] == null)
	  @						&& vals[x] == val);
	  @						//&& (hash(key) < x) ==> (\forall int y; hash(key) <= y && y < x;
	  @						//								keys[y] != null)
	  @						//&& (hash(key) > x) ==> ((\forall int y; hash(key) <= y && y < buckets;
	  @						//								keys[y] != null)
	  @						//					 		 && (\forall int y; 0 <= y && y < x;
	  @						//								keys[y] != null)));
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
		
		if (contains(key)) {
			int i = getIndex(iHash, key);
			if (i == -1) throw new IllegalArgumentException("nope");
			vals[i] = val;
			return;
		}
		
		int index = findEmpty(iHash);
		
		if (index != -1) {
			keys[index] = key;
			vals[index] = val;
			pairs++;
			return;
		}
		
		//Without resize we can't guarantee an empty bucket.
        //keys[iHash] = key;
        //vals[iHash] = val;
		overwriteValue(key, val, iHash);
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
	  @   requires 	\invariant_for(this);
	  @
	  @   //The given key is not in the table. (This can already be true at the beginning)
	  @   ensures	(\forall int x; 0 <= x && x < keys.length;
	  @					!(key.equals(keys[x])));
	  @
	  @   //If pairs is now pairs-1, then the key was in the hash table at the start of the method.
	  @   ensures	(pairs == \old(pairs) - 1) ==> 
	  @					(\exists int x; 0 <= x && x < keys.length;
	  @						\old(key.equals(keys[x])) && keys[x] == null && vals[x] == null);
	  @
	  @
	  @   //The method has no effect on hash table positions were the key wasn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < buckets && \old(!key.equals(keys[x]));
	  @					keys[x] == \old(keys[x]) && vals[x] == \old(vals[x]));
	  @
	  @
	  @
	  @ //The following is just a Copy of the Invariants. 
	  @ //The invariants them self are not checked.
	  @ //It only work in this way. Not sure why.
	  @ 
	  @   // The hash table has at least one chain.
	  @   ensures	buckets > 0;
	  @
	  @   //The arrays keys and vals are nonnull and are two different arrays.
	  @   ensures	keys != null && vals != null && keys != vals;
	  @
	  @   //The arrays keys and vals are not suptypes.
	  @   //It limits vals a bit, but helps verification.
	  @   //Maybe not important for linear probing.
	  @   ensures	\typeof(keys) == \type(HashObject[]) 
	  @						&& \typeof(vals) == \type(Object[]);
	  @
	  @   // The arrays keys and vals are equally long.
	  @   ensures	buckets == vals.length && buckets == keys.length;
	  @
	  @   //The hash table cant have a negative amount of elements.
	  @   //instance invariant	pairs == (\num_of int x; 0 <= x && x < keys.length; keys[x] != null);
	  @   //instance invariant	0 <= pairs && pairs < buckets;
	  @
	  @   //Each key is at most ones in the hash table.
	  @   ensures	(\forall int y; 0 <= y && y < keys.length && keys[y] != null;
	  @					(\forall int z; 0 < z && z < keys.length && keys[z] != null;
	  @						keys[z].equals(keys[y]) ==> (z == y)));
	  @
	  @   assignable keys[*], vals[*], pairs;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires key == null;
	  @   signals_only IllegalArgumentException;
	  @   signals (IllegalArgumentException e) true;
	  @*/
    public void /*@ helper*/ delete(HashObject key) {
		if (key == null)
			throw new IllegalArgumentException("argument to delete() is null");

		//int index = getIndex(hash(key), key);
		
		if (contains(key)) {
			int index = getIndex(hash(key), key);
			if (index == -1) throw new IllegalArgumentException("nope");
			keys[index] = null;
			vals[index] = null;
			pairs--;
		}
    }
	
	/*@ public normal_behavior
	  @   requires	key != null && val != null;
	  @   requires	0 <= index && index < buckets;
	  @   requires	(\forall int y; 0 <= y && y < keys.length;
	  @					!key.equals(keys[y]));
	  @   requires	!contains(key);
	  @
	  @   ensures	keys[index] == key && vals[index] == val;
	  @
	  @   assignable	keys[index], vals[index];
	  @*/
	private void overwriteValue(HashObject key, Object val, int index) {
		keys[index] = key;
		vals[index] = val;
	}
	
	/*@ public normal_behavior
	  @   requires 	\invariant_for(this);
	  @
	  @   //If the result is -1 the given key is not in the hash table.
	  @   ensures	!\result ==>
	  @					(\forall int x; 0 <= x && x < keys.length; 
	  @						!(key.equals(keys[x])));
	  @
	  @   //If the result is not -1 the given key is in the hash table 
	  @   //	and the result is the postion of the key.
	  @   ensures	\result ==> 
	  @					(\exists int x; 0 <= x && x < keys.length; 
	  @						key.equals(keys[x]));
	  @*/
	private /*@ strictly_pure @*/ boolean /*@ helper*/ contains(HashObject key) {
		/*@ //Every postion in the array up until now didnt include the key.
		  @ //	This is always true, since the method terminates if the key is found.
		  @ loop_invariant	0 <= j && j <= keys.length &&
		  @					(\forall int x; 0 <= x && x < j; 
		  @						!(key.equals(keys[x])));
		  @ assignable	\strictly_nothing;
		  @ decreases	keys.length - j;
		  @*/
		for (int j = 0; j < keys.length; j++) {
			if (key.equals(keys[j])) {
				return true;
			}
		}
		
		return false;
	}
}