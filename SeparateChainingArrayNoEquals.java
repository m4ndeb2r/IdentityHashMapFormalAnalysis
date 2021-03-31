/**
 * This implementation uses a separate chaining with arrays as collision
 * resolution strategy. When associating a value with a key that is already in
 * the hash table, the convention is to replace the old value with the new value.
 */
public class SeparateChainingArrayNoEquals {

	private static final int INIT_CAPACITY = 8;

	private int pairs; 								//number of key-value pairs
	private int chains; 							//hash table size
	private /*@ nullable @*/ HashObject[][] keys; 	//two dimensional array for keys
	private /*@ nullable @*/ Object[][] vals; 		//two dimensional array for values

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
	  @ //Each key is at most ones in the hash table.
	  @ //Only needs to check the same bucket because of the previous invariant.
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; 0 <= y && y < keys[x].length && keys[x][y] != null;
	  @								(\forall int z; y < z && z < keys[x].length && keys[x][z] != null;
	  @									keys[x][z] != (keys[x][y]))));
	  @
	  @
	  @
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
	public SeparateChainingArrayNoEquals() {
		this(INIT_CAPACITY);
	}

	/**
	 * Initializes an empty hash table with chains chains each with a size of 0.
	 * 
	 * @param chains
	 *            the initial number of chains, needs to be at least 1.
	 */
	public SeparateChainingArrayNoEquals(int chains) {
		if (chains < 1) chains = 1;
		pairs = 0;
		this.chains = chains;
		keys = new HashObject[chains][0];
		vals = new Object[chains][0];
	}
	
	// hash function for keys - returns value between 0 and chains-1
	/*@ public normal_behavior
	  @   requires	chains > 0;
	  @   ensures	(\forall HashObject ho; key == ho 
	  @					==> (\result == hash(ho)))
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
		if (number == Integer.MIN_VALUE) return 0;
		if (number < 0) return -number;
		return number;
	}

	//Returns the index of the given key, if the key is in the hash table.
	//Otherwise returns -1.
	/*@ public normal_behavior
	  @   requires 	0 <= iHash && iHash < chains;
	  @
	  @   //If the result is -1 the given key is not in the hash table.
	  @   ensures	(\result == -1) ==>
	  @					(\forall int x; 0 <= x && x < keys[iHash].length; 
	  @						!(key == (keys[iHash][x])));
	  @
	  @   //If the result is not -1 the given key is in the hash table 
	  @   //	and the result is the postion of the key.
	  @   ensures	(\result != -1) ==> 
	  @					(0 <= \result && \result < keys[iHash].length 
	  @					&& key == (keys[iHash][\result]));
	  @*/
	private /*@ strictly_pure @*/ int getIndex(int iHash, HashObject key) {
		/*@ //Every postion in the array up until now didnt include the key.
		  @ //	This is always true, since the method terminates if the key is found.
		  @ loop_invariant	0 <= j && j <= keys[iHash].length &&
		  @					(\forall int x; 0 <= x && x < j; 
		  @						!(key == (keys[iHash][x])));
		  @ assignable	\strictly_nothing;
		  @ decreases	keys[iHash].length - j;
		  @*/
		for (int j = 0; j < keys[iHash].length; j++) {
			if (key == (keys[iHash][j])) {
				return j;
			}
		}
		return -1;
	}
	
	//Increases the size of the chain iHash by one and 
	//adds the given key-value pair to the chain.
	/*@ public normal_behavior
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	getIndex(iHash, key) == -1;
	  @
	  @   //The new arrays are still the correct typ.
	  @   ensures	\typeof(keys[iHash]) == \type(HashObject[])
	  @				&& \typeof(vals[iHash]) == \type(Object[]);
	  @
	  @   //The array size did increase by one.
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
	private void increaseArraySize(int iHash, HashObject key, Object val) {
		keys[iHash] = increaseAndCopyKeys(keys[iHash], key);
		vals[iHash] = increaseAndCopyVals(vals[iHash], val);
		pairs++;
	}
	
	//Increases the given array by one and adds the element to the table.
	/*@ public normal_behavior
	  @   //The new arrays are still the correct typ and is a new array.
	  @   ensures	\typeof(\result) == \type(HashObject[])
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
	private HashObject[] increaseAndCopyKeys(HashObject[] array, HashObject element) {
		int len = array.length;
		HashObject[] temp = new HashObject[len + 1];
		
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
	  @   //The new arrays are still the correct typ and is a new array.
	  @   ensures	\typeof(\result) == \type(Object[])
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
	private Object[] increaseAndCopyVals(Object[] array, Object element) {
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
	  @   requires	(\forall int x; 0 <= x && x < chains;
	  @					(\forall int y; 0 <= y && y < keys[x].length;
	  @						(keys[x][y] != null) ==> (vals[x][y] != null)));
	  @
	  @   //If the result is not null, the key is in keys
	  @   //	and the result is at the same postion in vals.
	  @   ensures	(\result != null) ==>
      @   				(\exists int x; 0 <= x && x < keys[hash(key)].length;
	  @						key == (keys[hash(key)][x]) 
	  @						&& vals[hash(key)][x] == \result);
	  @
	  @   //If the result is null, the key is not in keys.
	  @   ensures	(\result == null) ==> 
      @					(\forall int x; 0 <= x && x < keys[hash(key)].length;
	  @						!(key == (keys[hash(key)][x])));
	  @   
	  @   //We can't make the whole method strictly pure, 
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
		if (key == null) throw new IllegalArgumentException("argument to get() is null");

		int iHash = hash(key);
		int index = getIndex(iHash, key);

		if (index != -1) return vals[iHash][index];

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
	  @   ensures	key == (keys[hash(key)][\result]) && vals[hash(key)][\result] == val;
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
	  @
	  @   //The given key is not in the table. (This can already be true at the beginning)
	  @   ensures	(\forall int x; 0 <= x && x < keys[hash(key)].length;
	  @					!(key == (keys[hash(key)][x])));
	  @
	  @   //The method has no effect on hash table positions were the key wasn't placed.
	  @   ensures	(\forall int x; 0 <= x && x < keys[hash(key)].length && x != \result;
	  @						keys[hash(key)][x] == \old(keys[hash(key)][x]));
	  @
	  @   assignable keys[hash(key)][*], pairs;
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
			pairs--;
		}
		
		return index;
	}
}