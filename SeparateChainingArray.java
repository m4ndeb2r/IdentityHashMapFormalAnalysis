/**
 * This implementation uses a separate chaining with arrays as collision
 * resolution strategy. When associating a value with a key that is already in
 * the hash table, the convention is to replace the old value with the new value.
 */
public class SeparateChainingArray {

	private static final int INIT_CAPACITY = 8;

	private int pairs; 				// number of key-value pairs
	private int chains; 			// hash table size
	private HashObject[][] keys; 	// two dimensional array for keys
	private Object[][] vals; 		// two dimensional array for values

	/*@ // The hash table has at least one chain.
	  @ instance invariant	chains > 0;
	  @
	  @ //The hash table cant have a negative amount of elements.
	  @ // (?) pairs = #keys[x].length mit 0 <= x < chains
	  @ //instance invariant	pairs >= 0;
	  @
	  @ //The arrays keys and vals are nonnull and are two different arrays.
	  @ instance invariant	keys != null && vals != null && keys != vals;
	  @
	  @ //The arrays keys and vals are not suptypes.
	  @ //It limits vals a bit, but helps verification.
	  @ instance invariant	\typeof(keys) == \type(HashObject[][]) 
	  @						&& \typeof(vals) == \type(Object[][])
	  @						&& (\forall int x; 0 <= x && x < chains;
	  @							\typeof(vals[x]) == \type(Object[])
	  @							&& \typeof(keys[x]) == \type(HashObject[]));
	  @
	  @ // The arrays keys and vals are equally long.
	  @ instance invariant	chains == vals.length && chains == keys.length;
	  @
	  @ //Every element in keys or vals is nonnull.
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							keys[x] != null && vals[x] != null);
	  @
	  @ // Each array inside of keys has an equally long partner array in vals at the same postion
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							keys[x].length == vals[x].length);
	  @
	  @ //No two different postion in keys or vals have a reference to the same subarray. 
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; x < y && y < chains;
	  @								keys[x] != keys[y] && vals[x] != vals[y]));
	  @
	  @ //No array in keys appears in vals.
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; 0 <= y && y < chains;
	  @ 							keys[x] != vals[y]));
	  @
	  @ //Every element in keys[] or vals[] is nonnull.
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; 0 <= y && y < keys[x].length;
	  @								keys[x][y] != null && vals[x][y] != null));
	  @
	  @ //Each Key is in its correct bucket.
	  @ //instance invariant	(\forall int x; 0 <= x && x < chains;
	  @		//					(\forall int y; 0 <= y && y < keys[x].length;
	  @			//					x == hash(keys[x][y])));
	  @
	  @ //Each key is at most ones in the hash table.
	  @ //Only needs to check the same bucket because of the previous invariant.
	  @ //instance invariant	(\forall int x; 0 <= x && x < chains;
	  @		//					(\forall int y; 0 <= y && y < keys[x].length;
	  @			//					(\forall int z; 0 <= z && z < keys[x].length;
	  @				//					keys[x][z].equals(keys[x][y]) ==> (y == z))));
	  @*/

	/**
	 * Initializes an empty symbol table.
	 */
	public SeparateChainingArray() {
		this(INIT_CAPACITY);
	}

	/**
	 * Initializes an empty hash table with chains chains each with a size of 0.
	 * 
	 * @param chains
	 *            the initial number of chains, needs to be at least 1.
	 */
	public SeparateChainingArray(int chains) {
		if (chains < 1)
			chains = 1;
		pairs = 0;
		this.chains = chains;
		keys = new HashObject[chains][0];
		vals = new Object[chains][0];
	}

	//Returns the index of the given key, if the key is in the hash table.
	//Otherwise returns -1.
	/*@ public normal_behavior
	  @   requires 	0 <= valueH && valueH < chains;
	  @
	  @   //If the result is -1 the given key is not in the hash table.
	  @   ensures	(\result == -1) ==>
	  @					(\forall int x; 0 <= x && x < keys[valueH].length; 
	  @						!(key.equals(keys[valueH][x])));
	  @
	  @   //If the result is not -1 the given key is in the hash table 
	  @   //	and the result is the postion of the key.
	  @   ensures	(\result != -1) ==> 
	  @					(0 <= \result && \result < keys[valueH].length 
	  @					&& key.equals(keys[valueH][\result]));
	  @*/
	private /*@ strictly_pure @*/ int getIndex(int valueH, HashObject key) {
		/*@ //Every postion in the array up until now didnt include the key.
		  @ //	This is always true, since the method terminates if the key is found.
		  @ loop_invariant	0 <= j && j <= keys[valueH].length &&
		  @					(\forall int x; 0 <= x && x < j; 
		  @						!(key.equals(keys[valueH][x])));
		  @ assignable	\strictly_nothing;
		  @ decreases	keys[valueH].length - j;
		  @*/
		for (int j = 0; j < keys[valueH].length; j++) {
			if (key.equals(keys[valueH][j])) {
				return j;
			}
		}
		return -1;
	}
	
	/**
	 * Returns the value associated with the specified key in this hash table.
	 *
	 * @param key
	 *            the key
	 * @return the value associated with key in the hash table; null if no such
	 *         value
	 * @throws IllegalArgumentException
	 *             if key is null
	 */
	/*@ public normal_behavior
	  @   //If the result is not null, the key is in keys
	  @   //	and the result is at the same postion in vals.
	  @   ensures	(\result != null) ==>
      @   				(\exists int x; 0 <= x && x < keys[hash(key)].length;
	  @						key.equals(keys[hash(key)][x]) 
	  @						&& vals[hash(key)][x] == \result);
	  @
	  @   //If the result is null, the key is not in keys.
	  @   ensures	(\result == null) ==> 
      @					(\forall int x; 0 <= x && x < keys[hash(key)].length;
	  @						!(key.equals(keys[hash(key)][x])));
	  @   
	  @   //We can't make the whole method strictly_pure, 
	  @   //because a exception creates an object.
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

		int valueH = hash(key);
		int index = getIndex(valueH, key);

		if (index != -1) {
			return vals[valueH][index];
		}

		return null;
	}
	
	/*@ public normal_behavior
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	(getIndex(iHash, key) == -1);
	  @
	  @   ensures	keys[iHash][keys[iHash].length - 1] == key
	  @				&& vals[iHash][vals[iHash].length - 1] == val
	  @				&& (\forall int x; 0 <= x && x < keys[iHash].length - 1; 
	  @					keys[iHash][x] == \old(keys[iHash][x])
	  @					&& vals[iHash][x] == \old(vals[iHash][x]));
	  @
	  @   assignable	keys[iHash], vals[iHash], pairs;
	  @*/
	private void increaseArraySize(int iHash, HashObject key, Object val) {
		int len = keys[iHash].length;
		HashObject[] keysTemp = new HashObject[len + 1];
		Object[] valsTemp = new Object[len + 1];
		
		/*@ //The arrays are a copys of the other arrays up until this point.
		  @ loop_invariant	0 <= k && k <= len &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @							keysTemp[x] == keys[iHash][x]
		  @							&& valsTemp[x] == vals[iHash][x]);
		  @ assignable	keysTemp[0 .. len-1], valsTemp[0 .. len-1];
		  @ decreases	len - k;
		  @*/
		for (int k = 0; k < len; k++) {
			keysTemp[k] = keys[iHash][k];
			valsTemp[k] = vals[iHash][k];
		}
		
		keysTemp[keysTemp.length - 1] = key;
		valsTemp[valsTemp.length - 1] = val;
		
		keys[iHash] = keysTemp;
		vals[iHash] = valsTemp;
	}
	
	/*@ public normal_behavior
	  @   requires	\invariant_for(this);
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	keys[iHash].length > 0;
	  @   requires	0 <= removePos && removePos < keys[iHash].length;
	  @
	  @   ensures	(\forall int x; 0 <= x && x < removePos; 
	  @					keys[iHash][x] == \old(keys[iHash][x])
	  @					&& vals[iHash][x] == \old(vals[iHash][x]));
	  @
	  @   ensures	(\forall int x; (removePos + 1) <= x && x < \old(keys[iHash].length); 
	  @					keys[iHash][x - 1] == \old(keys[iHash][x])
	  @					&& vals[iHash][x - 1] == \old(vals[iHash][x]));
	  @
	  @   assignable	keys[iHash], vals[iHash], pairs;
	  @
	  @ helper
	  @*/
	private void decreaseArraySize(int iHash, int removePos) {
		int len = keys[iHash].length;
		HashObject[] keysTemp = new HashObject[len - 1];
		Object[] valsTemp = new Object[len - 1];
		
		/*@ //The arrays are a copys of the other arrays up until this point.
		  @ loop_invariant	0 <= j && j <= removePos &&
		  @					(\forall int x; 0 <= x && x < j; 
		  @							keysTemp[x] == keys[iHash][x]
		  @							&& valsTemp[x] == vals[iHash][x]);
		  @ assignable	keysTemp[0 .. removePos-1], valsTemp[0 .. removePos-1];
		  @ decreases	removePos - j;
		  @*/
		for (int j = 0; j < removePos; j++) {
			keysTemp[j] = keys[iHash][j];
			valsTemp[j] = vals[iHash][j];
		}
		
		/*@ //The arrays are a copys of the other arrays up until this point.
		  @ loop_invariant	(removePos + 1) <= k && k <= len &&
		  @					(\forall int x; (removePos + 1) <= x && x < k; 
		  @							keysTemp[x - 1] == keys[iHash][x]
		  @							&& valsTemp[x - 1] == vals[iHash][x]);
		  @ assignable	keysTemp[removePos+1 .. len-1], valsTemp[removePos+1 .. len-1];
		  @ decreases	len - k;
		  @*/
		for (int k = removePos + 1; k < len; k++) {
			keysTemp[k - 1] = keys[iHash][k];
			valsTemp[k - 1] = vals[iHash][k];
		}
		
		keys[iHash] = keysTemp;
		vals[iHash] = valsTemp;
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
	  @   ensures	(\exists int x; 0 <= x && x < keys[hash(key)].length;
	  @					key.equals(keys[hash(key)][x]) && vals[hash(key)][x] == val);   
	  @
	  @   //The method has no effect on hash table positions were the key isn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < keys[hash(key)].length 
	  @					&& !key.equals(keys[hash(key)][x]);
	  @						keys[hash(key)][x] == \old(keys[hash(key)][x]) 
	  @						&& vals[hash(key)][x] == \old(vals[hash(key)][x]));
	  @
	  @   assignable	keys[hash(key)], vals[hash(key)], keys[hash(key)][*], vals[hash(key)][*], pairs;
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
		int index = getIndex(iHash, key);

		if (index != -1) {
			vals[iHash][index] = val;
			return;
		}
		
		increaseArraySize(iHash, key, val);
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
	/*@
	  @ public normal_behavior
	  @   //The given key is not in the table. (This can already be true at the beginning)
	  @   ensures	(\forall int x; 0 <= x && x < keys[hash(key)].length;
	  @					!(key.equals(keys[hash(key)][x])));
	  @
	  @   //The method has no effect on hash table positions were the key wasn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < keys[hash(key)].length 
	  @					&& \old(!key.equals(keys[hash(key)][x]));
	  @						keys[hash(key)][x] == \old(keys[hash(key)][x]) 
	  @						&& vals[hash(key)][x] == \old(vals[hash(key)][x]));
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

		int iHash = hash(key);
		int index = getIndex(iHash, key);

		if (index != -1) {
			HashObject[] keysTemp = new HashObject[keys[iHash].length - 1];
			Object[] valsTemp = new Object[vals[iHash].length - 1];

			keys[iHash] = keysTemp;
			vals[iHash] = valsTemp;
			pairs--;
		}
	}

	// hash function for keys - returns value between 0 and chains-1
	/*@ public normal_behavior
	  @   requires	chains > 0;
	  @   ensures	(\forall HashObject o; key.equals(o) 
	  @					==> (\result == hash(o)))
	  @				&& 0 <= \result && \result < chains;
	  @   ensures_free	\result == hash(key);
	  @   assignable	\strictly_nothing;
	  @   accessible	key.value, this.chains;
	  @
	  @ helper
	  @*/
	private /*@ strictly_pure @*/ int hash(HashObject key) {
		return abs(key.hashCode()) % chains;
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
}