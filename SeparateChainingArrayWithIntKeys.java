/**
 * This implementation uses a separate chaining with arrays as collision
 * resolution strategy. When associating a value with a key that is already in
 * the hash table, the convention is to replace the old value with the new value.
 */
public class SeparateChainingArrayWithIntKeys {

	private static final int INIT_CAPACITY = 8;
	private static final int iNull = 0;			//Null for int. This is not a valid key.

	private int pairs; 							//number of key-value pairs
	private int chains; 						//hash table size
	private int[][] keys; 						//two dimensional array for keys
	private /*@ nullable @*/ Object[][] vals; 	//two dimensional array for values

	/*@ //The hash table has at least one chain.
	  @ instance invariant	chains > 0;
	  @
	  @ //The arrays keys and vals are two different arrays.
	  @ instance invariant	keys != null && vals != null && keys != vals;
	  @
	  @ //The arrays keys and vals are not suptypes.
	  @ //Even with ints important, because arrays get overwritten.
	  @ instance invariant	\typeof(keys) == \type(int[][]) 
	  @						&& \typeof(vals) == \type(Object[][])
	  @						&& (\forall int x; 0 <= x && x < chains;
	  @							\typeof(vals[x]) == \type(Object[]));
	  @
	  @ //The arrays keys and vals are equally long.
	  @ instance invariant	chains == vals.length && chains == keys.length;
	  @
	  @ //Every element in keys or vals is nonnull.
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							keys[x] != null && vals[x] != null);
	  @
	  @ //Each array inside of keys has an equally long partner array in vals at the same postion.
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							keys[x].length == vals[x].length);
	  @
	  @ //No two different postion in keys or vals have a reference to the same subarray. 
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; x < y && y < chains;
	  @								keys[x] != keys[y] && vals[x] != vals[y]));
	  @
	  @ //No array in keys and vals have the same reference.
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; 0 <= y && y < chains;
	  @ 							keys[x] != vals[y]));
	  @
	  @ //pairs is the amount of key-value pairs in the hash table.
	  @ //Is important for resize which is currently not implemented.
	  @ //instance invariant	pairs == (\sum int x; 0 <= x && x < chains;
	  @	//								(\num_of int y; 0 <= y && y < keys[x].length;
	  @	//									keys[x][y] != iNull));
	  @
	  @ //Each key is at most ones in the same chain.
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; 0 <= y && y < keys[x].length && keys[x][y] != iNull;
	  @								(\forall int z; y < z && z < keys[x].length && keys[x][z] != iNull;
	  @									keys[x][z] != keys[x][y])));
	  @
	  @
	  @
	  @ //instance invariant	(\forall int x; 0 <= x && x < chains;
	  @		//					(\forall int y; 0 <= y && y < keys[x].length;
	  @			//					keys[x][y] != iNull &&  vals[x][y] != iNull));
	  @
	  @ //If a key is not null, then the value is also not null.
	  @ //	This is important for get(), since it returns null if the key is not in the table.
	  @ //instance invariant	(\forall int x; 0 <= x && x < chains;
	  @		//					(\forall int y; 0 <= y && y < keys[x].length;
	  @			//					(keys[x][y] != iNull) ==> (vals[x][y] != null)));
	  @
	  @ //Each Key is in its correct chain.
	  @ //instance invariant	(\forall int x; 0 <= x && x < chains;
	  @		//					(\forall int y; 0 <= y && y < keys[x].length;
	  @			//					x == hash(keys[x][y])));
	  @*/

	/**
	 * Initializes an empty symbol table.
	 */
	public SeparateChainingArrayWithIntKeys() {
		this(INIT_CAPACITY);
	}

	/**
	 * Initializes an empty hash table with chains chains each with a size of 0.
	 * 
	 * @param chains
	 *            the initial number of chains, needs to be at least 1.
	 */
	/*@ public normal_behavior
	  @   requires	chains > 0;
	  @
	  @   ensures	\fresh(keys) && \fresh(vals)
	  @				&& this.chains == chains && pairs == 0;
	  @
	  @   ensures	(\forall int x; 0 <= x && x < chains;
	  @					\fresh(keys[x]) && \fresh(vals[x]));
	  @
	  @   assignable	pairs, chains, keys, vals;
	  @*/
	public SeparateChainingArrayWithIntKeys(int chains) {
		if (chains < 1) chains = 1;
		pairs = 0;
		this.chains = chains;
		int[][] keysTemp = new int[chains][];
		Object[][] valsTemp = new Object[chains][];
		/*@ loop_invariant	0 <= j && j <= chains &&
		  @					(\forall int x; 0 <= x && x < j; 
		  @						\fresh(keysTemp[x]) && \fresh(valsTemp[x])
		  @						&& keysTemp[x].length == valsTemp[x].length
		  @						&& \typeof(valsTemp[x]) == \type(Object[])
		  @						&& keysTemp[x] != null && valsTemp[x] != null
		  @						&& (\forall int y; x < y && y < j;
		  @							keysTemp[x] != keysTemp[y] && valsTemp[x] != valsTemp[y])
		  @						&& (\forall int y; 0 <= y && y < j;
		  @							keysTemp[x] != valsTemp[y])
		  @						&& (\forall int y; 0 <= y && y < keysTemp[x].length 
		  @							&& keysTemp[x][y] != iNull;
		  @								(\forall int z; y < z && z < keysTemp[x].length 
		  @								&& keysTemp[x][z] != iNull;
		  @									keysTemp[x][z] != keysTemp[x][y])));
		  @ assignable	keysTemp[*], valsTemp[*];
		  @ decreases	chains - j;
		  @*/
		for (int j = 0; j < chains; j++) {
			keysTemp[j] = new int[0];
			valsTemp[j] = new Object[0];
		}
		
		keys = keysTemp;
		vals = valsTemp;
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

	//The int iHash is the hash value of the given key. The method returns 
	//the index of the given key, if the key is in the chain keys[iHash].
	//Otherwise returns -1.
	/*@ public normal_behavior
	  @   requires	key != iNull;
	  @   requires 	0 <= iHash && iHash < chains;
	  @
	  @   //If the result is -1 the given key is not in the given chain.
	  @   ensures	(\result == -1) ==>
	  @					(\forall int x; 0 <= x && x < keys[iHash].length; 
	  @						key != keys[iHash][x]);
	  @
	  @   //If the result is not -1 the given key is in the chain keys[iHash]
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
	
	//Increases the size of the chain keys[iHash] by one and 
	//adds the given key-value pair to the chain.
	/*@ public normal_behavior
	  @   requires	key != iNull;
	  @   requires	0 <= iHash && iHash < chains;
	  @
	  @   //The key is not in the chain keys[iHash].
	  @   requires	getIndex(iHash, key) == -1;
	  @
	  @   //The new arrays are still the correct typ.
	  @   ensures	\typeof(keys[iHash]) == \type(int[])
	  @				&& \typeof(vals[iHash]) == \type(Object[]);
	  @
	  @   //The array sizes did increase by one.
	  @   ensures	keys[iHash].length == (\old(keys[iHash].length) + 1)
	  @				&& vals[iHash].length == (\old(vals[iHash].length) + 1);
	  @
	  @   //The new array containts all old key-value pairs in the same order.
	  @   ensures	(\forall int x; 0 <= x && x < \old(keys[iHash].length); 
	  @					keys[iHash][x] == \old(keys[iHash][x])
	  @					&& vals[iHash][x] == \old(vals[iHash][x]));
	  @
	  @   //The new pair is the last element of the new arrays.
	  @   ensures	keys[iHash][keys[iHash].length - 1] == key
	  @				&& vals[iHash][vals[iHash].length - 1] == val;
	  @
	  @   assignable	keys[iHash], vals[iHash], pairs;
	  @*/
	private void increaseArraySize(int iHash, int key, Object val) {
		keys[iHash] = increaseAndCopyKeys(keys[iHash], key);
		vals[iHash] = increaseAndCopyVals(vals[iHash], val);
		pairs++;
	}
	
	//Increases the given array by one and adds the element to the table.
	/*@ public normal_behavior
	  @   //The new arrays are still the correct typ and is a new array.
	  @   ensures	\typeof(\result) == \type(int[])
	  @				&& \fresh(\result);
	  @
	  @   //The array size did increase by one.
	  @   ensures	\result.length == (array.length + 1);
	  @
	  @   //The new array containts all old elements in the same order.
	  @   ensures	(\forall int x; 0 <= x && x < array.length; 
	  @					\result[x] == array[x]);
	  @
	  @   //The new element is the last element of the new array.
	  @   ensures	\result[\result.length - 1] == element;
	  @
	  @   assignable	\nothing;
	  @
	  @ helper
	  @*/
	private int[] increaseAndCopyKeys(int[] array, int element) {
		int len = array.length;
		int[] temp = new int[len + 1];
		
		/*@ //The arrays are a copys of the other arrays up until this point.
		  @ loop_invariant	0 <= k && k <= len &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @							temp[x] == array[x]);
		  @ assignable	temp[0 .. len-1];
		  @ decreases	len - k;
		  @*/
		for (int k = 0; k < len; k++) {
			temp[k] = array[k];
		}
		
		temp[len] = element;
		
		return temp;
	}
	
	//Increases the given array by one and adds the element to the table.
	/*@ public normal_behavior
	  @   requires	array != null;
	  @
	  @   //The new arrays are still the correct typ and is a new array.
	  @   ensures	\typeof(\result) == \type(Object[])
	  @				&& \fresh(\result) && \result != null;
	  @
	  @   //The array size did increase by one.
	  @   ensures	\result.length == (array.length + 1);
	  @
	  @   //The new array containts all old elements in the same order.
	  @   ensures	(\forall int x; 0 <= x && x < array.length; 
	  @					\result[x] == array[x]);
	  @
	  @   //The new element is the last element of the new array.
	  @   ensures	\result[\result.length - 1] == element;
	  @
	  @   assignable	\nothing;
	  @
	  @ helper
	  @*/
	private /*@ nullable @*/ Object[] increaseAndCopyVals(/*@ nullable @*/ Object[] array, Object element) {
		int len = array.length;
		Object[] temp = new Object[len + 1];
		
		/*@ //The arrays are a copys of the other arrays up until this point.
		  @ loop_invariant	0 <= k && k <= len &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @							temp[x] == array[x]);
		  @ assignable	temp[0 .. len-1];
		  @ decreases	len - k;
		  @*/
		for (int k = 0; k < len; k++) {
			temp[k] = array[k];
		}
		
		temp[len] = element;
		
		return temp;
	}
	
	/**
	 * Returns the value associated with the given key in this hash table.
	 *
	 * @param key
	 *            the key
	 * @return the value associated with key in the hash table; 
	 *			null if no such  value
	 * @throws IllegalArgumentException
	 *             if key is null
	 */
	/*@ public normal_behavior
	  @    requires	key != iNull;
	  @
	  @    //If a key is not null, then the value is also not null.
	  @    requires	(\forall int x; 0 <= x && x < chains;
	  @					(\forall int y; 0 <= y && y < keys[x].length;
	  @						(keys[x][y] != iNull) ==> (vals[x][y] != null)));
	  @
	  @   //If the result is not null, the key is in keys
	  @   //	and the result is at the same postion in vals.
	  @   ensures	(\result != null) ==>
      @   				(\exists int x; 0 <= x && x < keys[hash(key)].length;
	  @						key == keys[hash(key)][x]
	  @						&& vals[hash(key)][x] == \result);
	  @
	  @   //If the result is null, the key is not in the hash table.
	  @   ensures	(\result == null) ==> 
      @					(\forall int x; 0 <= x && x < keys[hash(key)].length;
	  @						!(key == keys[hash(key)][x]));
	  @   
	  @   //We can't make the whole method strictly pure, 
	  @   //because an exception creates an object.
	  @   assignable	\strictly_nothing;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires	key == iNull;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
    public /*@ pure @*/ /*@ nullable @*/ Object get(int key) {
		if (key == iNull) 
			throw new IllegalArgumentException("The argument to get() is null");

		int iHash = hash(key);
		int index = getIndex(iHash, key);

		if (index != -1) return vals[iHash][index];

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
	  @   requires	key != iNull;
	  @
	  @   //The key-value pair is now in the hash table and at the same position.
	  @   ensures	key == keys[hash(key)][\result] && vals[hash(key)][\result] == val;
	  @
	  @   //The method has no effect on hash table positions were the key isn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < \old(keys[hash(key)].length) && x != \result;
	  @					keys[hash(key)][x] == \old(keys[hash(key)][x]) 
	  @					&& vals[hash(key)][x] == \old(vals[hash(key)][x]));
	  @
	  @   assignable	keys[hash(key)], vals[hash(key)], vals[hash(key)][*], pairs;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires	key == iNull || val == null;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
	public int put(int key, Object val) {
		if (key == iNull) 
			throw new IllegalArgumentException("The first argument to get() is null");
		if (val == null) 
			throw new IllegalArgumentException("The second argument to put() is null");

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
	 * Removes the given key from this hash table and therefore its 
	 * associated value inaccessible (if the key is in this hash table).
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
	  @   ensures	(\forall int x; 0 <= x && x < keys[hash(key)].length;
	  @					keys[hash(key)][x] != key);
	  @
	  @   //The method has no effect on hash table positions were the key wasn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < keys[hash(key)].length && x != \result; 
	  @					keys[hash(key)][x] == \old(keys[hash(key)][x]));
	  @
	  @   assignable keys[hash(key)][*], pairs;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires key == iNull;
	  @   signals_only IllegalArgumentException;
	  @   signals (IllegalArgumentException e) true;
	  @*/
	public int delete(int key) {
		if (key == iNull) 
			throw new IllegalArgumentException("The argument to delete() is null");

		int iHash = hash(key);
		int index = getIndex(iHash, key);

		if (index != -1) {
			keys[iHash][index] = iNull;
			pairs--;
		}
		
		return index;
	}
}