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
	  @ instance invariant	pairs >= 0;
	  @
	  @ //The arrays keys and vals are nonnull and are two different arrays.
	  @ instance invariant	keys != null && vals != null && keys != vals;
	  @
	  @ //The arrays keys and vals are not suptypes.
	  @ //It limits vals a bit, but helps verification.
	  @ instance invariant	\typeof(keys) == \type(HashObject[][]) 
	  @						&& \typeof(vals) == \type(Object[][])
	  @						&& (\forall int x; 0 <= x && x < chains;
	  @							\typeof(vals[x]) == \type(Object[]));
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
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; 0 <= y && y < keys[x].length;
	  @								x == hash(keys[x][y])));
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

	/*@ public normal_behavior
	  @   requires 	0 <= valueH && valueH < chains;
	  @
	  @   requires	\invariant_for(this);
	  @   //requires	(\forall int x; 0 <= x && x < chains;
	  @		//			(\forall int y; 0 <= y && y < keys[x].length;
	  @			//			(\forall int z; y < z && z < keys[x].length;
	  @				//			(keys[x][z].getValue() != keys[x][y].getValue()))));
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
	private /*@ strictly_pure @*/ int /*@ helper*/ getIndex(int valueH, HashObject key) {
		/*@ //Every postion in the array up until now didnt include the key.
		  @ //	This is always true, since the method terminates if the key is found.
		  @ loop_invariant	0 <= j && j <= keys[valueH].length &&
		  @					(\forall int x; 0 <= x && x < j; !(key.equals(keys[valueH][x])));
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
	
	/*@ public normal_behavior
	  @   requires 	0 <= valueH && valueH < chains;
	  @   ensures	\result ==> 
	  @					(\exists int x; 0 <= x && x < keys[valueH].length; 
	  @						(key.equals(keys[valueH][x])));
	  @   ensures	!\result ==> 
	  @					(\forall int x; 0 <= x && x < keys[valueH].length; 
	  @						!(key.equals(keys[valueH][x])));
	  @*/
	private /*@ strictly_pure @*/ boolean contains(int valueH, HashObject key) {
		/*@ //Every postion in the array up until now didnt include the key.
		  @ //	This is always true, since the method terminates if the key is found.
		  @ loop_invariant	0 <= j && j <= keys[valueH].length &&
		  @					(\forall int x; 0 <= x && x < j; !(key.equals(keys[valueH][x])));
		  @ assignable	\strictly_nothing;
		  @ decreases	keys[valueH].length - j;
		  @*/
		for (int j = 0; j < keys[valueH].length; j++) {
			if (key.equals(keys[valueH][j])) {
				return true;
			}
		}
		return false;
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
	/*@
	  @ public normal_behavior
	  @   requires	\invariant_for(this);
	  @   requires	(\forall int x; 0 <= x && x < chains;
	  @					(\forall int y; 0 <= y && y < keys[x].length;
	  @						(\forall int z; y < z && z < keys[x].length;
	  @							(keys[x][z].getValue() != keys[x][y].getValue()))));
	  @
	  @   ensures	(\result != null) ==>
      @   				(\exists int y; 0 <= y && y < keys[hash(key)].length;
	  @						key.equals(keys[hash(key)][y]) && vals[hash(key)][y] == \result);
	  @   ensures	(\result == null) ==> 
      @					(\forall int y; 0 <= y && y < keys[hash(key)].length;
	  @						!(key.equals(keys[hash(key)][y])));
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

		int valueH = hash(key);
		int index = getIndex(valueH, key);

		if (index != -1) {
			return vals[valueH][index];
		}

		return null;
	}
	
	/*@
	  @ public normal_behavior
	  @   requires	\invariant_for(this);
	  @
	  @   requires	keysTemp != null && valsTemp != null && keysTemp != valsTemp;
	  @   requires	keysTemp.length == valsTemp.length;
	  @   requires	\typeof(keysTemp) == \type(HashObject[]) 
	  @				&& \typeof(valsTemp) == \type(Object[]);
	  @   requires	\typeof(keysTemp) == \typeof(keys[iHash])
	  @				&& \typeof(valsTemp) == \typeof(vals[iHash]);
	  @
	  @   requires	(\forall int x; 0 <= x && x < chains;
	  @					keysTemp != keys[x] && keysTemp != vals[x]
	  @					&& valsTemp != keys[x] && valsTemp != vals[x]);
	  @
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	0 <= srcPos && 0 <= destPos && 0 <= length;
	  @   requires	length + srcPos <= keys[iHash].length 
	  @				&& length + destPos <= keysTemp.length;
	  @
	  @   ensures	(\forall int x; 0 <= x && x < length; 
	  @					keysTemp[destPos + x] == keys[iHash][srcPos + x]
	  @					&& valsTemp[destPos + x] == vals[iHash][srcPos + x]);
	  @
	  @   assignable	valsTemp[destPos .. destPos+length-1], keysTemp[destPos .. destPos+length-1];
	  @*/
	private void /*@ helper*/ arrayCopy(HashObject[] keysTemp, Object[] valsTemp, int iHash, int srcPos, int destPos, int length) {
		/*@ //The arrays are a copys of the other arrays up until this point.
		  @ loop_invariant	0 <= k && k <= length &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @						keysTemp[destPos + x] == keys[iHash][srcPos + x] 
		  @						&& valsTemp[destPos + x] == vals[iHash][srcPos + x]);
		  @ assignable	valsTemp[destPos .. destPos+length-1], keysTemp[destPos .. destPos+length-1];
		  @ decreases	length - k;
		  @*/
		for (int k = 0; k < length; k++) {
			keysTemp[destPos + k] = keys[iHash][srcPos + k];
			valsTemp[destPos + k] = vals[iHash][srcPos + k];
		}
		return;
	}
	
	/*@ public normal_behavior
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	(\forall int x; 0 <= x && x < keys[iHash].length; 
	  @						(key.getValue() != keys[iHash][x].getValue()));
	  @
	  @   requires	(\forall int y; 0 <= y && y < keys[iHash].length;
	  @					(\forall int z; y < z && z < keys[iHash].length;
	  @						(keys[iHash][z].getValue() != keys[iHash][y].getValue())));
	  @
	  @   ensures	pairs == \old(pairs) + 1
	  @				&& keys[iHash].length == \old(keys[iHash].length) + 1
	  @				&& vals[iHash].length == \old(vals[iHash].length) + 1
	  @				&& keys[iHash][keys[iHash].length - 1] == key
	  @				&& vals[iHash][vals[iHash].length - 1] == val
	  @				&& (\forall int x; 0 <= x && x < keys[iHash].length - 1; 
	  @					keys[iHash][x] == \old(keys[iHash][x])
	  @					&& vals[iHash][x] == \old(vals[iHash][x]));
	  @
	  @   ensures	(\forall int y; 0 <= y && y < keys[iHash].length;
	  @					(\forall int z; y < z && z < keys[iHash].length;
	  @						(keys[iHash][z].getValue() != keys[iHash][y].getValue())));
	  @
	  @   assignable	keys[iHash], vals[iHash], pairs;
	  @*/
	private void increaseArraySize(int iHash, HashObject key, Object val) {
		HashObject[] keysTemp = increaseKeysSize(keys[iHash]);
		Object[] valsTemp = increaseValsSize(vals[iHash]);
		
		keysTemp[keysTemp.length - 1] = key;
		valsTemp[valsTemp.length - 1] = val;
		
		keys[iHash] = keysTemp;
		vals[iHash] = valsTemp;
		pairs++;
	}
	
	/*@ public normal_behavior
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	(\forall int x; 0 <= x && x < keys[iHash].length; 
	  @						(key.getValue() != keys[iHash][x].getValue()));
	  @
	  @   requires	(\forall int y; 0 <= y && y < keys[iHash].length;
	  @					(\forall int z; y < z && z < keys[iHash].length;
	  @						(keys[iHash][z].getValue() != keys[iHash][y].getValue())));
	  @
	  @   ensures	keys[iHash].length == \old(keys[iHash].length) + 1
	  @				&& keys[iHash][keys[iHash].length - 1] == key
	  @				&& (\forall int x; 0 <= x && x < keys[iHash].length - 1; 
	  @					keys[iHash][x] == \old(keys[iHash][x]));
	  @
	  @   ensures	(\forall int y; 0 <= y && y < keys[iHash].length;
	  @					(\forall int z; y < z && z < keys[iHash].length;
	  @						(keys[iHash][z].getValue() != keys[iHash][y].getValue())));
	  @
	  @   assignable	keys[iHash];
	  @*/
	private void updateKeys(int iHash, HashObject key) {
		HashObject[] keysTemp = increaseKeysSize(keys[iHash]);
		
		keysTemp[keysTemp.length - 1] = key;
		
		keys[iHash] = keysTemp;
	}
	
	/*@ public normal_behavior
	  @   requires	0 <= iHash && iHash < chains;
	  @
	  @   requires	(\forall int y; 0 <= y && y < keys[iHash].length;
	  @					(\forall int z; y < z && z < keys[iHash].length;
	  @						(keys[iHash][z].getValue() != keys[iHash][y].getValue())));
	  @
	  @   ensures	vals[iHash].length == \old(vals[iHash].length) + 1
	  @				&& vals[iHash][vals[iHash].length - 1] == val
	  @				&& (\forall int x; 0 <= x && x < vals[iHash].length - 1; 
	  @					vals[iHash][x] == \old(vals[iHash][x]));
	  @
	  @   ensures	(\forall int y; 0 <= y && y < keys[iHash].length;
	  @					(\forall int z; y < z && z < keys[iHash].length;
	  @						(keys[iHash][z].getValue() != keys[iHash][y].getValue())));
	  @
	  @   assignable	vals[iHash];
	  @*/
	private void updateVals(int iHash, Object val) {
		Object[] valsTemp = increaseValsSize(vals[iHash]);
		
		valsTemp[valsTemp.length - 1] = val;

		vals[iHash] = valsTemp;
	}
	
	/*@ public normal_behavior
	  @
	  @   //Should be true, because of the invariants.
	  @   //keysToCopy is supposed to be a keys[hash(key)].
	  @   requires	keysToCopy != null;
	  @   requires	(\forall int x; 0 <= x && x < keysToCopy.length; 
	  @					keysToCopy[x] != null);
	  @   requires	(\forall int y; 0 <= y && y < keysToCopy.length;
	  @					(\forall int z; y < z && z < keysToCopy.length;
	  @						(keysToCopy[z].getValue() != keysToCopy[y].getValue())));
	  @   
	  @   //Needs to hold for the invariants.
	  @   ensures	\result != null;
	  @   ensures	(\forall int x; 0 <= x && x < \result.length - 1; 
	  @					\result[x] != null);
	  @   ensures	(\forall int y; 0 <= y && y < \result.length - 1;
	  @					(\forall int z; y < z && z < \result.length - 1;
	  @						(keysToCopy[z].getValue() != keysToCopy[y].getValue())));
	  @
	  @   //What the method does.
	  @   ensures	\result.length == keysToCopy.length + 1;
	  @   ensures	(\forall int x; 0 <= x && x < \result.length - 1; 
	  @					\result[x] == keysToCopy[x]);
	  @   ensures	\typeof(\result) == \type(HashObject[]);
	  @
	  @   assignable	\nothing;
	  @*/
	private HashObject[] /*@ helper*/ increaseKeysSize(HashObject[] keysToCopy) {
		int len = keysToCopy.length;
		HashObject[] keysTemp = new HashObject[len + 1];
		
		/*@ //The arrays are a copys of the other arrays up until this point.
		  @ loop_invariant	0 <= k && k <= len &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @							keysTemp[x] == keysToCopy[x]);
		  @ assignable	keysTemp[0 .. len-1];
		  @ decreases	len - k;
		  @*/
		for (int k = 0; k < len; k++) {
			keysTemp[k] = keysToCopy[k];
		}
		
		//The contract doesn't work without this.
		keysTemp[len] = new HashObject(0);
		
		return keysTemp;
	}
	
	/*@ public normal_behavior
	  @   
	  @   //Should be true, because of the invariants.
	  @   //valsToCopy is supposed to be a vals[hash(key)].
	  @   requires	valsToCopy != null;
	  @   requires	(\forall int x; 0 <= x && x < valsToCopy.length; 
	  @					valsToCopy[x] != null);
	  @
	  @   //Needs to hold for the invariants.
	  @   ensures	\result != null;
	  @   ensures	(\forall int x; 0 <= x && x < \result.length - 1; 
	  @					\result[x] != null);
	  @
	  @    //What the method does.
	  @   ensures	\result.length == valsToCopy.length + 1;
	  @   ensures	(\forall int x; 0 <= x && x < \result.length - 1; 
	  @					\result[x] == valsToCopy[x]);
	  @   ensures	\typeof(\result) == \type(Object[]);
	  @
	  @   assignable	\nothing;
	  @*/
	private Object[] /*@ helper*/ increaseValsSize(Object[] valsToCopy) {
		int len = valsToCopy.length;
		Object[] valsTemp = new Object[len + 1];
		
		/*@ //The arrays are a copys of the other arrays up until this point.
		  @ loop_invariant	0 <= k && k <= len &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @							valsTemp[x] == valsToCopy[x]);
		  @ assignable	valsTemp[0 .. len-1];
		  @ decreases	len - k;
		  @*/
		for (int k = 0; k < len; k++) {
			valsTemp[k] = valsToCopy[k];
		}
		
		//The contract doesn't work without this.
		valsTemp[len] = new Object();
		
		return valsTemp;
	}
	
	/*@ public normal_behavior
	  @   requires	val != null;
	  @   requires	0 <= iHash && iHash < chains;
	  @   requires	0 <= index && index < vals[iHash].length;
	  @
	  @   requires	(\forall int y; 0 <= y && y < keys[iHash].length;
	  @					(\forall int z; y < z && z < keys[iHash].length;
	  @						(keys[iHash][z].getValue() != keys[iHash][y].getValue())));
	  @
	  @   ensures	vals[iHash][index] == val;
	  @
	  @   ensures	(\forall int y; 0 <= y && y < keys[iHash].length;
	  @					(\forall int z; y < z && z < keys[iHash].length;
	  @						(keys[iHash][z].getValue() != keys[iHash][y].getValue())));
	  @
	  @   assignable	vals[iHash][index];
	  @*/
	private void overwriteValue(Object val, int iHash, int index) {
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
	  @   requires	(\forall int y; 0 <= y && y < keys[hash(key)].length;
	  @					(\forall int z; y < z && z < keys[hash(key)].length;
	  @						(keys[hash(key)][z].getValue() != keys[hash(key)][y].getValue())));
	  @   
	  @   //The amount of elements in the hash table (called pairs) is now either pairs or pairs+1.
	  @   ensures	(pairs == \old(pairs)) || (pairs == \old(pairs) + 1);
	  @   
	  @   //If pairs is now pairs, then the key was and still is in the table and the given value is at this postion.
	  @   //	The current contract might not hold if resize is used, 
	  @   //	since the contract requires that the keys postion did not change.
	  @   ensures	(pairs == \old(pairs)) ==>
	  @					(keys[hash(key)].length == \old(keys[hash(key)].length)
	  @					&& (\exists int x; 0 <= x && x < keys[hash(key)].length;
	  @						key.equals(keys[hash(key)][x]) && \old(key.equals(keys[hash(key)][x]))
	  @						&& vals[hash(key)][x] == val));
	  @   
	  @   //If pairs is now pairs+1, then the table size at the keys postion (hash(key)) did increase by 1 and
	  @   //	the key-value-pair is now at the new postion. (Duplicate was already checked)
	  @   ensures	(pairs == \old(pairs) + 1) ==>
	  @					((keys[hash(key)].length == (\old(keys[hash(key)].length) + 1)) 
	  @						&& keys[hash(key)][keys[hash(key)].length-1].equals(key)
	  @						&& vals[hash(key)][vals[hash(key)].length-1] == val);
	  @
	  @   ensures	(\forall int y; 0 <= y && y < keys[hash(key)].length;
	  @					(\forall int z; y < z && z < keys[hash(key)].length;
	  @						(keys[hash(key)][z].getValue() != keys[hash(key)][y].getValue())));
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
			//overwriteValue(val, iHash, index);
			return;
		}
		
		//increaseArraySize(iHash, key, val);
		
		//HashObject[] keysTemp = increaseKeysSize(keys[iHash]);
		
		keys[iHash] = increaseKeysSize(keys[iHash]);
		vals[iHash] = increaseValsSize(vals[iHash]);
		
		keys[iHash][keys[iHash].length - 1] = key;
		vals[iHash][vals[iHash].length - 1] = val;
		
		pairs++;
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
	  @   requires true;
	  @
	  @   //The given key is not in the table. (This can already be true at the beginning)
	  @   ensures (\forall int x; 0 <= x && x < keys[hash(key)].length;
	  @			   !(keys[hash(key)][x].equals(key)));
	  @
	  @   //The amount of elements in the hash table (called n) is now either n or n-1.
	  @   ensures (pairs == \old(pairs)) || (pairs == \old(pairs) - 1);
	  @
	  @   //If pairs is now pairs-1, then the key was in the hash table at the start of the method and
	  @   //	the table size at the keys postion did decrease be 1.
	  @   ensures (pairs == \old(pairs) - 1) ==> 
	  @			   ((\exists int x; 0 <= x && x < keys[hash(key)].length;
	  @				   \old(keys[hash(key)][x].equals(key)))
	  @			   && (keys[hash(key)].length == \old(keys[hash(key)].length) - 1));
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
			
			arrayCopy(keysTemp, valsTemp, iHash, 0, 0, index);
			arrayCopy(keysTemp, valsTemp, iHash, index + 1, index, keys[iHash].length - index - 1);

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
	  @*/
	private /*@ strictly_pure @*/ int /*@ helper*/ hash(HashObject key) {
		//return (key.hashCode() * key.hashCode()) % chains;
		return abs(key.hashCode()) % chains;
		//return ((key.hashCode() % chains) + chains) % chains;
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
}