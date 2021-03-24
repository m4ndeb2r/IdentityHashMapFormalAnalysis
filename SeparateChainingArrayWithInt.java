/**
 * This implementation uses a separate chaining with arrays as collision
 * resolution strategy. When associating a value with a key that is already in
 * the hash table, the convention is to replace the old value with the new value.
 */
public class SeparateChainingArrayWithInt {

	private static final int INIT_CAPACITY = 8;
	private static final int iNull = Integer.MIN_VALUE;

	private int pairs; 				// number of key-value pairs
	private int chains; 			// hash table size
	private int[][] keys; 			// two dimensional array for keys
	private int[][] vals; 			// two dimensional array for values

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
	  @ //Even with ints important, because of overwriting arrays.
	  @ instance invariant	\typeof(keys) == \type(int[][]) 
	  @						&& \typeof(vals) == \type(int[][])
	  @						&& (\forall int x; 0 <= x && x < chains;
	  @							\typeof(vals[x]) == \type(int[])
	  @							&& \typeof(keys[x]) == \type(int[]));
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
	  @ //instance invariant	(\forall int x; 0 <= x && x < chains;
	  @		//					(\forall int y; 0 <= y && y < keys[x].length;
	  @			//					keys[x][y] != iNull &&  vals[x][y] != iNull));
	  @
	  @ //If a key is not null, then the value is also not null.
	  @ //	This is important for get(), since it returns null if the key is not in the table.
	  @ //instance invariant	(\forall int x; 0 <= x && x < chains;
	  @		//					(\forall int y; 0 <= y && y < keys[x].length;
	  @			//					(keys[x][y] != iNull) ==> (vals[x][y] != iNull)));
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
	  @				//					keys[x][z] == keys[x][y] ==> (y == z))));
	  @
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; 0 <= y && y < keys[x].length && keys[x][y] != iNull;
	  @								(\forall int z; y < z && z < keys[x].length && keys[x][z] != iNull;
	  @									keys[x][z] != keys[x][y])));
	  @*/

	/**
	 * Initializes an empty symbol table.
	 */
	public SeparateChainingArrayWithInt() {
		this(INIT_CAPACITY);
	}

	/**
	 * Initializes an empty hash table with chains chains each with a size of 0.
	 * 
	 * @param chains
	 *            the initial number of chains, needs to be at least 1.
	 */
	public SeparateChainingArrayWithInt(int chains) {
		if (chains < 1)
			chains = 1;
		pairs = 0;
		this.chains = chains;
		keys = new int[chains][0];
		vals = new int[chains][0];
	}

	//Returns the index of the given key, if the key is in the hash table.
	//Otherwise returns -1.
	/*@ public normal_behavior
	  @   requires	key != iNull;
	  @   requires 	0 <= iHash && iHash < chains;
	  @
	  @   //If the result is -1 the given key is not in the hash table.
	  @   ensures	(\result == -1) ==>
	  @					(\forall int x; 0 <= x && x < keys[iHash].length; 
	  @						key != keys[iHash][x]);
	  @
	  @   //If the result is not -1 the given key is in the hash table 
	  @   //	and the result is the postion of the key.
	  @   ensures	(\result != -1) ==> 
	  @					(0 <= \result && \result < keys[iHash].length 
	  @					&& key == keys[iHash][\result]);
	  @*/
	private /*@ strictly_pure @*/ int getIndex(int iHash, int key) {
		/*@ //Every postion in the array up until now didnt include the key.
		  @ //	This is always true, since the method terminates if the key is found.
		  @ loop_invariant	0 <= j && j <= keys[iHash].length &&
		  @					(\forall int x; 0 <= x && x < j; 
		  @						key != keys[iHash][x]);
		  @ assignable	\strictly_nothing;
		  @ decreases	keys[iHash].length - j;
		  @*/
		for (int j = 0; j < keys[iHash].length; j++) {
			if (key == keys[iHash][j]) return j;
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
	  @    requires	key != iNull;
	  @
	  @   //If the result is not null, the key is in keys
	  @   //	and the result is at the same postion in vals.
	  @   ensures	(\result != iNull) ==>
      @   				(\exists int x; 0 <= x && x < keys[hash(key)].length;
	  @						key == keys[hash(key)][x]
	  @						&& vals[hash(key)][x] == \result);
	  @
	  @   //If the result is null, the key is not in keys.
	  @   ensures	(\result == iNull) ==> 
      @					(\forall int x; 0 <= x && x < keys[hash(key)].length;
	  @						!(key == keys[hash(key)][x]));
	  @   
	  @   //We can't make the whole method strictly_pure, 
	  @   //because a exception creates an object.
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

		int iHash = hash(key);
		int index = getIndex(iHash, key);

		if (index != -1) return vals[iHash][index];

		return iNull;
	}
	
	
	/*@ public normal_behavior
	  @   requires	key != iNull && vals != iNull;
	  @   requires	0 <= iHash && iHash < chains;
  	  @   //requires	iHash == hash(key);
	  @   requires	(getIndex(iHash, key) == -1);
	  @
	  @   ensures	\typeof(keys[iHash]) == \type(int[])
	  @				&& \typeof(vals[iHash]) == \type(int[]);
	  @
	  @   ensures	keys[iHash].length == (\old(keys[iHash].length) + 1)
	  @				&& vals[iHash].length == (\old(vals[iHash].length) + 1);
	  @
	  @   ensures	(\forall int x; 0 <= x && x < \old(keys[iHash].length); 
	  @					keys[iHash][x] == \old(keys[iHash][x])
	  @					&& vals[iHash][x] == \old(vals[iHash][x]));
	  @
	  @   ensures	keys[iHash][keys[iHash].length - 1] == key
	  @				&& vals[iHash][vals[iHash].length - 1] == val;
	  @
	  @   assignable	keys[iHash], vals[iHash];
	  @*/
	private void increaseArraySize(int iHash, int key, int val) {
		int len = keys[iHash].length;
		int[] keysTemp = new int[len + 1];
		int[] valsTemp = new int[len + 1];
		
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
	  @   //ensures	(\forall int x; 0 <= x && x < keys[iHash].length; 
	  @		//			keys[iHash][x] != \old(keys[iHash][removePos]));
	  @
	  @   //ensures	(\forall int x; 0 <= x && x < \old(keys[iHash].length) && x != removePos; 
	  @		//			(\exists int y; 0 <= y && y < keys[iHash].length; 
	  @			//			\old(keys[iHash][x]) == keys[iHash][y]));
	  @
	  @   ensures	keys[iHash].length == (\old(keys[iHash].length) - 1)
	  @				&& vals[iHash].length == (\old(vals[iHash].length) - 1);
	  @
	  @   ensures	\typeof(keys[iHash]) == \type(int[])
	  @				&& \typeof(vals[iHash]) == \type(int[]);
	  @
	  @   assignable	keys[iHash], vals[iHash];
	  @
	  @ helper
	  @*/
	private void decreaseArraySize(int iHash, int removePos) {
		int len = keys[iHash].length;
		int[] keysTemp = new int[len - 1];
		int[] valsTemp = new int[len - 1];
		
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
	  @
	  @   ensures	(\forall int x; 0 <= x && x < keys[iHash].length;
	  @					!(keys[iHash][x] == \old(keys[iHash][keys[iHash].length - 1])));
	  @
	  @   ensures	(\forall int x; 0 <= x && x < \old(keys[iHash].length) - 1; 
	  @					(\exists int y; 0 <= y && y < keys[iHash].length; 
	  @						\old(keys[iHash][x]) == keys[iHash][y]
	  @						&& \old(vals[iHash][x]) == vals[iHash][y]));
	  @
	  @   //ensures	(\forall int x; 0 <= x && x < (\old(keys[iHash].length) - 1); 
	  @		//			keys[iHash][x] == \old(keys[iHash][x])
	  @			//		&& vals[iHash][x] == \old(vals[iHash][x]));
	  @
	  @   ensures	keys[iHash].length == (\old(keys[iHash].length) - 1)
	  @				&& vals[iHash].length == (\old(vals[iHash].length) - 1);
	  @
	  @   ensures	\typeof(keys[iHash]) == \type(int[])
	  @				&& \typeof(vals[iHash]) == \type(int[]);
	  @
	  @   assignable	keys[iHash], vals[iHash];
	  @*/
	private void removeLastElement(int iHash) {
		int len = keys[iHash].length;
		int[] keysTemp = new int[len - 1];
		int[] valsTemp = new int[len - 1];
		
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
		int keyTemp = keys[iHash][swapPosition];
		int valTemp = vals[iHash][swapPosition];
		
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
	  @
	  @   ensures	(\forall int x; 0 <= x && x < keys[iHash].length;
	  @					!(keys[iHash][x] == \old(keys[iHash][removePos])));
	  @
	  @  ensures	(\forall int x; 0 <= x && x < \old(keys[iHash].length) && x != removePos;
	  @					(\exists int y; 0 <= y && y < keys[iHash].length; 
	  @						\old(keys[iHash][x]) == keys[iHash][y]
	  @						&& \old(vals[iHash][x]) == vals[iHash][y]));
	  @
	  @   //ensures	(\forall int x; 0 <= x && x < (\old(keys[iHash].length) - 1) && x != removePos; 
	  @		//			keys[iHash][x] == \old(keys[iHash][x])
	  @			//		&& vals[iHash][x] == \old(vals[iHash][x]));
	  @
	  @   ensures	keys[iHash].length == (\old(keys[iHash].length) - 1)
	  @				&& vals[iHash].length == (\old(vals[iHash].length) - 1);
	  @
	  @   ensures	\typeof(keys[iHash]) == \type(int[])
	  @				&& \typeof(vals[iHash]) == \type(int[]);
	  @
	  @   //ensures	keys[iHash][removePos] == \old(keys[iHash][keys[iHash].length - 1])
	  @		//		&& vals[iHash][removePos] == \old(vals[iHash][vals[iHash].length - 1]);
	  @
	  @
	  @   assignable	keys[iHash], vals[iHash], keys[iHash][*], vals[iHash][*];
	  @*/
	private void decreaseArraySize2(int iHash, int removePos) {
		swapToLast(iHash, removePos);
		removeLastElement(iHash);
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
	  @   ensures	key == keys[hash(key)][\result] && vals[hash(key)][\result] == val;
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
	  @   requires	val == iNull;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
	public int put(int key, int val) {
		if (val == iNull) throw new IllegalArgumentException("second argument to put() is null");

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
	  @   requires	key != iNull;
	  @
	  @   //The given key is not in the table. (This can already be true at the beginning)
	  @   ensures	(\forall int x; 0 <= x && x < keys[hash(key)].length;
	  @					keys[hash(key)][x] != key);
	  @
	  @   //The method has no effect on hash table positions were the key wasn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < keys[hash(key)].length && x != \result; 
	  @					keys[hash(key)][x] == \old(keys[hash(key)][x])
	  @					&& vals[hash(key)][x] == \old(vals[hash(key)][x]));
	  @
	  @   assignable keys[hash(key)][*], vals[hash(key)][*], pairs;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires key == null;
	  @   signals_only IllegalArgumentException;
	  @   signals (IllegalArgumentException e) true;
	  @*/
	public int delete(int key) {
		if (key == iNull) throw new IllegalArgumentException("argument to delete() is null");

		int iHash = hash(key);
		int index = getIndex(iHash, key);

		if (index != -1) {
			keys[iHash][index] = iNull;
			vals[iHash][index] = iNull;
			pairs--;
		}
		
		return index;
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
	  @   requires	(\exists int x; 0 <= x && x < keys[hash(key)].length;
	  @					keys[hash(key)][x] == iNull);
	  @
	  @   ensures	key == keys[hash(key)][\result] && vals[hash(key)][\result] == val;
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
	  @   requires	val == iNull;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
	public int put2(int key, int val) {
		if (val == iNull) throw new IllegalArgumentException("second argument to put() is null");

		int iHash = hash(key);
		int index = getIndex(iHash, key);

		if (index != -1) {
			vals[iHash][index] = val;
			return index;
		}
		
		insertPair(key, val, iHash);
		return keys[iHash].length - 1;
	}
	
	//Simply overwrites a key-value pair. This is a method, because it is difficult
	//to verifiy this part of the hash table, specifically the invariants.
	/*@ public normal_behavior
	  @   requires	key != iNull && val != iNull;
	  @   requires	(getIndex(iHash, key) == -1);
	  @   requires	iHash == hash(key);
	  @   requires	(\exists int x; 0 <= x && x < keys[iHash].length;
	  @					keys[iHash][x] == iNull);
	  @
	  @   //The key-value pair is now in the hash table and at the same position. 
	  @   ensures	key == keys[iHash][\result] && vals[iHash][\result] == val;
	  @
	  @   //The method has no effect on hash table positions were the key isn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < keys[iHash].length && x != \result;
	  @					keys[iHash][x] == \old(keys[iHash][x]) 
	  @					&& vals[iHash][x] == \old(vals[iHash][x]));
	  @
	  @   assignable	keys[iHash][*], vals[iHash][*], pairs;
	  @*/
	private int insertPair(int key, int val, int iHash) {
		int index = findEmpty(iHash);
		keys[iHash][index] = key;
		vals[iHash][index] = val;
		pairs++;
		return index;
	}
	
	//Returns the index of an null-entry, if one is in the hash table.
	//	It starts its search from iHash which is the hash-value of a key.
	//  This is to essential to the hashtable concept.
	//	I originally used one loop with the modulo operator, but the 
	//	current two loop version is easier to verifiy.
	//Otherwise returns -1.
	/*@ public normal_behavior
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	(\exists int x; 0 <= x && x < keys[iHash].length;
	  @					keys[iHash][x] == iNull);
	  @
	  @   //The result is always an index of the array and at this index
	  @   //is a null.
	  @   ensures	0 <= \result && \result < keys[iHash].length 
	  @				&& iNull == keys[iHash][\result];
	  @*/
	private /*@ strictly_pure @*/ int findEmpty(int iHash) {
		/*@ //Every postion in the array up until now is not null.
		  @ //	This is always true, since the method terminates if a null bucket is found.
		  @ loop_invariant	0 <= j && j <= keys[iHash].length &&
		  @					(\forall int x; 0 <= x && x < j; 
		  @						keys[iHash][x] != iNull);
		  @ assignable	\strictly_nothing;
		  @ decreases	keys[iHash].length - j;
		  @*/
		for (int j = 0; j < keys[iHash].length; j++) {
			if (keys[iHash][j] == iNull) return j;
		}
		
		//Should never be reached.
		return -1;
	}

	// hash function for keys - returns value between 0 and chains-1
	/*@ public normal_behavior
	  @   requires	chains > 0 && key != iNull;
	  @   ensures	(\forall int i; key == i ==> (\result == hash(i)))
	  @				&& 0 <= \result && \result < chains;
	  @   ensures_free	\result == hash(key);
	  @   assignable	\strictly_nothing;
	  @   accessible	this.chains;
	  @
	  @ helper
	  @*/
	private /*@ strictly_pure @*/ int hash(int key) {
		return abs(key) % chains;
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
}