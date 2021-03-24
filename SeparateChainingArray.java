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
	  @ //Currently doesn't work with delete, but the pairs 
	  @ //variable is important for resize.
	  @ //instance invariant	pairs >= 0;
	  @
	  @ //The arrays keys and vals are two different arrays.
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
	  @ //If a key is not null, then the value is also not null.
	  @ //	This is important for get(), since it returns null if the key is not in the table.
	  @ //instance invariant	(\forall int x; 0 <= x && x < chains;
	  @		//					(\forall int y; 0 <= y && y < keys[x].length;
	  @			//					(keys[x][y] != null) ==> (vals[x][y] != null)));
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
	  @				&& vals[iHash][vals[iHash].length - 1] == val;
	  @
	  @   ensures	(\forall int x; 0 <= x && x < \old(keys[iHash].length); 
	  @					keys[iHash][x] == \old(keys[iHash][x])
	  @					&& vals[iHash][x] == \old(vals[iHash][x]));
	  @
	  @   ensures	keys[iHash].length == (\old(keys[iHash].length) + 1)
	  @				&& vals[iHash].length == (\old(vals[iHash].length) + 1);
	  @
	  @   ensures	\typeof(keys[iHash]) == \type(HashObject[])
	  @				&& \typeof(vals[iHash]) == \type(Object[]);	
	  @
	  @   assignable	keys[iHash], vals[iHash];
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
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	keys[iHash].length > 0;
	  @   requires	0 <= removePos && removePos < keys[iHash].length;
	  @
	  @   ensures	getIndex(iHash, \old(keys[iHash][removePos])) == -1;
	  @
	  @   ensures	(\forall int x; 0 <= x && x < \old(keys[iHash].length) && x != removePos; 
	  @					getIndex(iHash, \old(keys[iHash][x])) != -1);
	  @
	  @   ensures	keys[iHash].length == (\old(keys[iHash].length) - 1)
	  @				&& vals[iHash].length == (\old(vals[iHash].length) - 1);
	  @
	  @   ensures	\typeof(keys[iHash]) == \type(HashObject[])
	  @				&& \typeof(vals[iHash]) == \type(Object[]);
	  @
	  @   assignable	keys[iHash], vals[iHash];
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
		  @ assignable	keysTemp[removePos .. len-2], valsTemp[removePos .. len-2];
		  @ decreases	len - k;
		  @*/
		for (int k = removePos + 1; k < len; k++) {
			keysTemp[k - 1] = keys[iHash][k];
			valsTemp[k - 1] = vals[iHash][k];
		}
		
		keys[iHash] = keysTemp;
		vals[iHash] = valsTemp;
	}
	
	/*@ public normal_behavior
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	keys[iHash].length > 0;
	  @   requires	(\forall int y; 0 <= y && y < keys[iHash].length;
	  @					(\forall int z; 0 <= z && z < keys[iHash].length;
	  @						keys[iHash][z].equals(keys[iHash][y]) ==> (y == z)));
	  @
	  @   ensures	(\forall int x; 0 <= x && x < keys[iHash].length;
	  @					!(keys[iHash][x].equals(\old(keys[iHash][keys[iHash].length - 1]))));
	  @
	  @   ensures	(\forall int x; 0 <= x && x < (\old(keys[iHash].length) - 1); 
	  @					keys[iHash][x] == \old(keys[iHash][x])
	  @					&& vals[iHash][x] == \old(vals[iHash][x]));
	  @
	  @   ensures	keys[iHash].length == (\old(keys[iHash].length) - 1)
	  @				&& vals[iHash].length == (\old(vals[iHash].length) - 1);
	  @
	  @   ensures	\typeof(keys[iHash]) == \type(HashObject[])
	  @				&& \typeof(vals[iHash]) == \type(Object[]);
	  @
	  @   assignable	keys[iHash], vals[iHash];
	  @*/
	private void removeLastElement(int iHash) {
		int len = keys[iHash].length;
		HashObject[] keysTemp = new HashObject[len - 1];
		Object[] valsTemp = new Object[len - 1];
		
		/*@ //The arrays are a copys of the other arrays up until this point.
		  @ loop_invariant	0 <= j && j <= len - 1 &&
		  @					(\forall int x; 0 <= x && x < j; 
		  @							keysTemp[x] == keys[iHash][x]
		  @							&& valsTemp[x] == vals[iHash][x]);
		  @ assignable	keysTemp[0 .. len-2], valsTemp[0 .. len-2];
		  @ decreases	len - 1 - j;
		  @*/
		for (int j = 0; j < len - 1; j++) {
			keysTemp[j] = keys[iHash][j];
			valsTemp[j] = vals[iHash][j];
		}
		
		keys[iHash] = keysTemp;
		vals[iHash] = valsTemp;
	}
	
	/*@ public normal_behavior
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	keys[iHash].length > 0;
	  @   requires	0 <= swapPosition && swapPosition < keys[iHash].length;
	  @
	  @   ensures	keys[iHash][swapPosition] == \old(keys[iHash][keys[iHash].length - 1])
	  @				&& vals[iHash][swapPosition] == \old(vals[iHash][vals[iHash].length - 1])
	  @				&& keys[iHash][keys[iHash].length - 1] == \old(keys[iHash][swapPosition])
	  @				&& vals[iHash][vals[iHash].length - 1] == \old(vals[iHash][swapPosition]);
	  @
	  @   assignable	keys[iHash][swapPosition], vals[iHash][swapPosition],
	  @					keys[iHash][keys[iHash].length - 1], vals[iHash][vals[iHash].length - 1];
	  @*/
	private void swapToLast(int iHash, int swapPosition) {
		HashObject keyTemp = keys[iHash][swapPosition];
		Object valTemp = vals[iHash][swapPosition];
		
		keys[iHash][swapPosition] = keys[iHash][keys[iHash].length - 1];
		vals[iHash][swapPosition] = vals[iHash][vals[iHash].length - 1];
		
		keys[iHash][keys[iHash].length - 1] = keyTemp;
		vals[iHash][vals[iHash].length - 1] = valTemp;
	}
	
	/*@ public normal_behavior
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	keys[iHash].length > 0;
	  @   requires	0 <= removePos && removePos < keys[iHash].length;
	  @
	  @   //Not possible because we dont check for duplicates.
	  @   //ensures	(\forall int x; 0 <= x && x < keys[iHash].length;
	  @		//			!(keys[iHash][x].equals(\old(keys[iHash][removePos]))));
	  @
	  @   //ensures	(\forall int x; 0 <= x && x < keys[iHash].length && x != removePos;
	  @		//				keys[iHash][x] == \old(keys[iHash][x]) 
	  @			//			&& vals[iHash][x] == \old(vals[iHash][x]));
	  @
	  @   ensures	keys[iHash][removePos] == \old(keys[iHash][keys[iHash].length - 1])
	  @				&& vals[iHash][removePos] == \old(vals[iHash][vals[iHash].length - 1]);
	  @
	  @   ensures	keys[iHash].length == (\old(keys[iHash].length) - 1)
	  @				&& vals[iHash].length == (\old(vals[iHash].length) - 1);
	  @
	  @   ensures	\typeof(keys[iHash]) == \type(HashObject[])
	  @				&& \typeof(vals[iHash]) == \type(Object[]);
	  @
	  @   assignable	keys[iHash], vals[iHash], keys[iHash][*], vals[iHash][*];
	  @*/
	private void decreaseArraySize2(int iHash, int removePos) {
		swapToLast(iHash, removePos);
		removeLastElement(iHash);
	}
	
	/*@ public normal_behavior
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	keys[iHash].length > 0;
	  @   requires	0 <= index && index < keys[iHash].length;
	  @   //requires	iHash == hash(key);
	  @
	  @   ensures	keys[iHash][index] == key && vals[iHash][index] == val;
	  @
	  @   assignable	keys[iHash][index], vals[iHash][index];
	  @*/
	private void overwritePair(HashObject key, Object val, int iHash, int index) {
		keys[iHash][index] = key;
		vals[iHash][index] = val;
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
	  @   ensures	key.equals(keys[hash(key)][\result]) && vals[hash(key)][\result] == val;
	  @
	  @   //The method has no effect on hash table positions were the key isn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < \old(keys[hash(key)].length) && x != \result;
	  @					keys[hash(key)][x] == \old(keys[hash(key)][x]) 
	  @					&& vals[hash(key)][x] == \old(vals[hash(key)][x]));
	  @
	  @   assignable	keys[hash(key)], vals[hash(key)], vals[hash(key)][*];
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires	key == null || val == null;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
	public int put(HashObject key, Object val) {
		if (key == null) throw new IllegalArgumentException("first argument to put() is null");
		if (val == null) throw new IllegalArgumentException("second argument to put() is null");

		int iHash = hash(key);
		int index = getIndex(iHash, key);

		if (index != -1) {
			vals[iHash][index] = val;
			return index;
		}
		
		increaseArraySize(iHash, key, val);
		return keys[iHash].length - 1;
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
	  @   //requires	(\forall int y; 0 <= y && y < keys[hash(key)].length;
	  @		//			(\forall int z; y < z && z < keys[hash(key)].length;
	  @			//			keys[hash(key)][z].getValue() != keys[hash(key)][y].getValue()));
	  @
	  @   //The given key is not in the table. (This can already be true at the beginning)
	  @   //ensures	(\forall int x; 0 <= x && x < keys[\result].length;
	  @		//			!(key.getValue() == keys[\result][x].getValue()));
	  @
	  @   //The method has no effect on hash table positions were the key wasn't placed.
	  @   //ensures	(\forall int x; 0 <= x && x < keys[\result].length
	  @		//			&& \old(!(key.getValue() == keys[\result][x].getValue()));
	  @			//			keys[\result][x] == \old(keys[\result][x]) 
	  @				//		&& vals[\result][x] == \old(vals[\result][x]));
	  @
	  @   //The method has no effect on hash table positions were the key wasn't placed.
	  @   //ensures	(\forall int x; 0 <= x && x < keys[hash(key)].length && x != \result;
	  @		//				keys[hash(key)][x] == \old(keys[hash(key)][x]) 
	  @			//			&& vals[hash(key)][x] == \old(vals[hash(key)][x]));
	  @   //ensures	(\result != -1) ==>
	  @		//			(keys[hash(key)][\result] == null 
	  @			//		&& vals[hash(key)][\result] == null);
	  @
	  @   assignable keys[hash(key)][*], vals[hash(key)][*], pairs;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires key == null;
	  @   signals_only IllegalArgumentException;
	  @   signals (IllegalArgumentException e) true;
	  @*/
	public int delete(HashObject key) {
		if (key == null) throw new IllegalArgumentException("argument to delete() is null");

		int iHash = hash(key);
		int index = getIndex(iHash, key);

		if (index != -1) {
			
			
			keys[iHash][index] = null;
			vals[iHash][index] = null;
			pairs--;
		}
		return iHash;
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