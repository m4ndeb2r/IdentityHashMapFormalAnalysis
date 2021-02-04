/**
 * This implementation uses a separate chaining with arrays as collision
 * resolution strategy. It supports the usual put, get, contains, delete, size
 * and is-empty methods. When associating a value with a key that is already in
 * the hash table, the convention is to replace the old value with the new
 * value.
 */
public class SeparateChainingArray {

	private static final int INIT_CAPACITY = 8;

	private int pairs; 				// number of key-value pairs
	private int chains; 			// hash table size
	private HashObject[][] keys; 	// two dimensional array for keys
	private Object[][] vals; 		// two dimensional array for vals

	/*@ // The hash table has at least one chain.
	  @ instance invariant	chains > 0;
	  @
	  @ //The hash table cant have a negative amount of elements.
	  @ instance invariant	pairs >= 0;
	  @
	  @ //The arrays keys and vals are nonnull and are two different arrays.
	  @ instance invariant	keys != null && vals != null && keys != vals;
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
	  @ //Every element in keys[] or vals[] is nonnull.
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; 0 <= y && y < keys[x].length;
	  @								keys[x][y] != null && vals[x][y] != null));
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
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; 0 <= y && y < keys[x].length;
	  @								x == hash(keys[x][y])));
	  @
	  @ //Each key is at most ones in the hash table.
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; 0 <= y && y < keys[x].length;
	  @								(\forall int z; 0 <= z && z < keys[x].length;
	  @									keys[x][z].equals(keys[x][y]) ==> (y == z))));
	  @*/

	/**
	 * Initializes an empty symbol table.
	 */
	public SeparateChainingArray() {
		this(INIT_CAPACITY);
	}

	/**
	 * Initializes an empty hash table with m chains each with a size of len.
	 * 
	 * @param chains
	 *            the initial number of chains, needs to be at least 1.
	 * @throws IllegalArgumentException
	 *             if chains or length is smaller then 1
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
	  @   requires 	0 <= valueH && valueH < chains && \invariant_for(this);
	  @
	  @   //The result is -1 if and only if the given key is not in the hash table.
	  @   ensures	(\result == -1) ==>
	  @					(\forall int x; 0 <= x && x < keys[valueH].length; 
	  @						!(key.equals(keys[valueH][x])));
	  @
	  @   //The result is not -1 if and only if the given key is in the hash table 
	  @   //	and the result is postion of the key.
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
	
	//RunTimeExceptions
	//IndexOutOfBoundsException - if copying would cause access of data outside array bounds.
	//NullPointerException - if either src or dest is null.
	/*@
	  @ public normal_behavior
	  @   requires	keysTemp != null && valsTemp != null;
	  @   requires	keysTemp != keys[valueH] && keysTemp != vals[valueH]
	  @				&& keysTemp != valsTemp && valsTemp != vals[valueH];
	  @   requires	keysTemp.length == valsTemp.length;
	  @   requires	\typeof(keysTemp) == \type(HashObject[]);
	  @   requires	\typeof(keysTemp) == \typeof(keys[valueH])
	  @				&& \typeof(valsTemp) == \typeof(vals[valueH]);
	  @	  requires	0 <= valueH && valueH < chains;
	  @   requires	0 <= srcPos && srcPos < keys[valueH].length;
	  @   requires	0 <= destPos && destPos < keysTemp.length;
	  @   requires	0 <= length && length + srcPos <= keys[valueH].length 
	  @				&& length + destPos <= keysTemp.length;
	  @   ensures	(\forall int x; 0 <= x && x < length; 
	  @					keysTemp[destPos + x] == keys[valueH][srcPos + x]
	  @					&& valsTemp[destPos + x] == vals[valueH][srcPos + x]);
	  @   assignable	valsTemp[destPos .. destPos+length-1], keysTemp[destPos .. destPos+length-1];
	  @*/
	private void arrayCopy(HashObject[] keysTemp, Object[] valsTemp, int valueH, int srcPos, int destPos, int length) {
		/*@ //The arrays are a copys of the other arrays up until this point.
		  @ loop_invariant	0 <= k && k <= length &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @						keysTemp[destPos + x] == keys[valueH][srcPos + x] 
		  @						&& valsTemp[destPos + x] == vals[valueH][srcPos + x]);
		  @ assignable	valsTemp[destPos .. destPos+length-1], keysTemp[destPos .. destPos+length-1];
		  @ decreases	length - k;
		  @*/
		for (int k = 0; k < length; k++) {
			keysTemp[destPos + k] = keys[valueH][srcPos + k];
			valsTemp[destPos + k] = vals[valueH][srcPos + k];
		}
		return;
	}
	
	//RunTimeExceptions
	//IndexOutOfBoundsException - if copying would cause access of data outside array bounds.
	//NullPointerException - if either src or dest is null.
	/*@
	  @ public normal_behavior
	  @   requires	keysTemp != null;
	  @   requires	\typeof(keysTemp) == \type(HashObject[]);
	  @   requires	0 <= i && i < chains;
	  @   requires	keysTemp != keys[i];
	  @   requires	\typeof(keysTemp) == \typeof(keys[i]);
	  @   requires	0 <= srcPos && srcPos < keys[i].length;
	  @   requires	0 <= destPos && destPos < keysTemp.length;
	  @   requires	0 <= length && length + srcPos <= keys[i].length 
	  @				&& length + destPos <= keysTemp.length;
	  @   ensures	(\forall int x; 0 <= x && x < length; 
	  @					keysTemp[destPos + x] == keys[i][srcPos + x]);
	  @   assignable	keysTemp[destPos .. destPos+length-1];
	  @*/
	private void arrayCopy(HashObject[] keysTemp, int i ,int srcPos, int destPos, int length) {
		/*@ //The arrays are a copys of the other arrays up until this point.
		  @ loop_invariant	0 <= k && k <= length &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @						keysTemp[destPos + x] == keys[i][srcPos + x]);
		  @ assignable	keysTemp[destPos .. destPos+length-1];
		  @ decreases	length - k;
		  @*/
		for (int k = 0; k < length; k++) {
			keysTemp[destPos + k] = keys[i][srcPos + k];
		}
		return;
	}

	/**
	 * Inserts the specified key-value pair into the hash table, overwriting the old
	 * value with the new value if the hash table already contains the specified
	 * key. Sets the occupied flag to false (and therefore delete) the specified key
	 * (and its associated value) from this hash table if the specified value is
	 * null.
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
	  @   ensures	((pairs == \old(pairs)) <=!=> (pairs == \old(pairs) + 1));
	  @   
	  @   //If pairs is now pairs, then the key was and still is in the table and the given value is at this postion.
	  @   //	The current contract might not hold if resize is used, 
	  @   //	since the contract requires that the keys postion did not change.
	  @   ensures	(pairs == \old(pairs)) ==>
	  @					(\exists int x; 0 <= x && x < keys[hash(key)].length;
	  @						keys[hash(key)][x].equals(key) && \old(keys[hash(key)][x].equals(key))
	  @						&& vals[hash(key)][x] == val);
	  @   
	  @   //If pairs is now pairs+1, then the table size at the keys postion (hash(key)) did increase by 1 and
	  @   //	the key-value-pair is now at the new postion. (Duplicate was already checked)
	  @   ensures	(pairs == \old(pairs) + 1) ==>
	  @					((keys[hash(key)].length == \old(keys[hash(key)].length) + 1) 
	  @						&& keys[hash(key)][keys[hash(key)].length-1].equals(key)
	  @						&& vals[hash(key)][vals[hash(key)].length-1] == val);
	  @
	  @   assignable	keys[*], vals[*], vals[hash(key)][*], pairs;
	  @
	  @ also
	  @ exceptional_behavior
	  @   requires	key == null || val == null;
	  @   signals_only	IllegalArgumentException;
	  @   signals	(IllegalArgumentException e) true;
	  @*/
	public void put(HashObject key, Object val) {
		if (key == null)
			throw new IllegalArgumentException("first argument to put() is null");
		if (val == null)
			throw new IllegalArgumentException("second argument to put() is null");

		int hash = hash(key);
		int index = getIndex(hash, key);

		if (index != -1) {
			vals[hash][index] = val;
			return;
		}

		HashObject[] keysTemp = new HashObject[keys[hash].length + 1];
		Object[] valsTemp = new Object[vals[hash].length + 1];
		
		arrayCopy(keysTemp, valsTemp, hash, 0, 0, keys[hash].length);

		keysTemp[keys[hash].length] = key;
		valsTemp[vals[hash].length] = val;

		keys[hash] = keysTemp;
		vals[hash] = valsTemp;
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
	  @   //he given key is not in the table. (This can already be true at the beginning)
	  @   ensures (\forall int x; 0 <= x && x <= keys[hash(key)].length;
	  @			   !(keys[hash(key)][x].equals(key)));
	  @
	  @   //The amount of elements in the hash table (called n) is now either n or n-1.
	  @   ensures (pairs == \old(pairs)) <=!=> (pairs == \old(pairs) - 1);
	  @
	  @   //If pairs is now pairs-1, then the key was in the hash table at the start of the method and
	  @   //	the table size at the keys postion did decrease be 1.
	  @   ensures (pairs == \old(pairs) - 1) ==> 
	  @			   ((\exists int x; 0 <= x && x <= \old(keys[hash(key)].length);
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

		int hash = hash(key);
		int index = getIndex(hash, key);

		if (index != -1) {
			HashObject[] keysTemp = new HashObject[keys[hash].length - 1];
			Object[] valsTemp = new Object[vals[hash].length - 1];
			
			arrayCopy(keysTemp, valsTemp, hash, 0, 0, index);
			arrayCopy(keysTemp, valsTemp, hash, index + 1, index, keys[hash].length - index - 1);

			keys[hash] = keysTemp;
			vals[hash] = valsTemp;
			pairs--;
		}
	}

	// hash function for keys - returns value between 0 and chains-1
	/*@ public normal_behavior
	  @   requires	chains > 0;
	  @   ensures	(\forall HashObject o; key.equals(o) 
	  @					==> (\result == hash(o)))
	  @				&& 0 <= \result && \result < chains;
	  @   //ensures_free	\result == hash(key);
	  @   assignable	\strictly_nothing;
	  @   //accessible	key.*, this.chains;
	  @*/
	private /*@ strictly_pure @*/ int /*@ helper*/ hash(HashObject key) {
		return abs(key.hashCode()) % chains;
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

public final class HashObject {

	private final int value;

	public HashObject(int value) {
		this.value = value;
	}

	public final /*@ strictly_pure @*/ int getValue() {
		return value;
	}

	public final /*@ strictly_pure @*/ int hashCode() {
		return value;
	}

	public final /*@ strictly_pure @*/ boolean equals(/*@ nullable @*/ Object otherObject) {
		if (!(otherObject instanceof HashObject)) return false;
		return this.value == ((HashObject) otherObject).getValue();
	}
}