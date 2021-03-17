/**
 * This implementation uses a separate chaining with arrays as collision
 * resolution strategy. When associating a value with a key that is already in
 * the hash table, the convention is to replace the old value with the new value.
 */
public class SeparateChainingArrayWithInt {

	private static final int INIT_CAPACITY = 8;

	private int pairs; 				// number of key-value pairs
	private int chains; 			// hash table size
	private int[][] keys; 			// two dimensional array for keys
	private int[][] vals; 		// two dimensional array for values

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
	  @							(\forall int y; 0 <= y && y < keys[x].length;
	  @								(\forall int z; y < z && z < keys[x].length;
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
	  @   requires 	0 <= valueH && valueH < chains;
	  @
	  @   //If the result is -1 the given key is not in the hash table.
	  @   ensures	(\result == -1) ==>
	  @					(\forall int x; 0 <= x && x < keys[valueH].length; 
	  @						key != keys[valueH][x]);
	  @
	  @   //If the result is not -1 the given key is in the hash table 
	  @   //	and the result is the postion of the key.
	  @   ensures	(\result != -1) ==> 
	  @					(0 <= \result && \result < keys[valueH].length 
	  @					&& key == keys[valueH][\result]);
	  @*/
	private /*@ strictly_pure @*/ int getIndex(int valueH, int key) {
		/*@ //Every postion in the array up until now didnt include the key.
		  @ //	This is always true, since the method terminates if the key is found.
		  @ loop_invariant	0 <= j && j <= keys[valueH].length &&
		  @					(\forall int x; 0 <= x && x < j; 
		  @						key != keys[valueH][x]);
		  @ assignable	\strictly_nothing;
		  @ decreases	keys[valueH].length - j;
		  @*/
		for (int j = 0; j < keys[valueH].length; j++) {
			if (key == keys[valueH][j]) {
				return j;
			}
		}
		return -1;
	}
	
	/*@ public normal_behavior
	  @   requires	0 <= iHash && iHash < chains;
  	  @   requires	iHash == hash(key);
	  @   requires	(getIndex(iHash, key) == -1);
	  @   requires	(\forall int y; 0 <= y && y < keys[iHash].length;
	  @					iHash == hash(keys[iHash][y]));
	  @
	  @   ensures	(\forall int y; 0 <= y && y < keys[iHash].length;
	  @					iHash == hash(keys[iHash][y]));
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
	  @   ensures	\typeof(vals[iHash]) == \type(int[]);	
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
	  @   requires	val == null;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
	public int put(int key, int val) {
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

	// hash function for keys - returns value between 0 and chains-1
	/*@ public normal_behavior
	  @   requires	chains > 0;
	  @   ensures	(\forall int i; key == i ==> (\result == hash(i)))
	  @				&& 0 <= \result && \result < chains;
	  @   ensures_free	\result == hash(key);
	  @   assignable	\strictly_nothing;
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