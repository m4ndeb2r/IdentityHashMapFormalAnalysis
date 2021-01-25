/**
 * This implementation uses a separate chaining with arrays as collision
 * resolution strategy. It supports the usual put, get, contains, delete, size
 * and is-empty methods. When associating a value with a key that is already in
 * the hash table, the convention is to replace the old value with the new
 * value.
 */
public class SeparateChainingArray {

	private static final int INIT_CAPACITY = 8;

	private int n; 					// number of key-value pairs
	private int chains; 			// hash table size
	private HashObject[][] keys; 	// two dimensional array for keys
	private Object[][] vals; 		// two dimensional array for vals

	/*@ // The hash table has at least one chain.
	  @ instance invariant	chains > 0;
	  @
	  @ //The hash table cant have a negative amount of elements.
	  @ instance invariant	n >= 0;
	  @
	  @ //The arrays keys and vals are nonnull.
	  @ instance invariant	keys != null && vals != null;
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
	  @ //   (No arrays aliasing)
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; x < y && y < chains;
	  @								keys[x] != keys[y] && vals[x] != vals[y]));
	  @
	  @ //Each Key is in its correct bucket.
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; 0 <= y && y < keys[x].length;
	  @								x == hash(keys[x][y])));
	  @
	  @ //Each key is exactly ones in the hash table.
	  @ //Removed the exists, because of the first two foralls.
	  @ instance invariant	(\forall int x; 0 <= x && x < chains;
	  @							(\forall int y; 0 <= y && y < keys[x].length;
	  @								(\forall int z; 0 <= z && z <= keys[x].length;
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
		n = 0;
		this.chains = chains;
		keys = new HashObject[chains][0];
		vals = new Object[chains][0];
	}

	/*@ public normal_behavior
	  @   requires 	0 <= i && i < chains;
	  @ 
	  @   //The result is -1 if and only if the given key is not in the hash table.
	  @   ensures	(\result == -1) <==>
	  @					(\forall int x; 0 <= x && x < keys[i].length; 
	  @						!(keys[i][x].equals(key)));
	  @
	  @   //The result is not -1 if and only if the given key is in the hash table 
	  @   //	and the result is postion of the key.
	  @   ensures	(\result != -1) <==> 
	  @					(\exists int y; 0 <= y && y < keys[i].length;
	  @						keys[i][y].equals(key) && y == \result);
	  @
	  @   assignable	\strictly_nothing;
	  @*/
	private int getIndex(int i, HashObject key) {
		/*@ //Every postion in the array up until now didnt include the key.
		  @ //	This is always true, since the method terminates if the key is found.
		  @ loop_invariant	0 <= j && j <= keys[i].length &&
		  @					(\forall int x; 0 <= x && x < j; !(keys[i][x].equals(key)));
		  @ assignable	\strictly_nothing;
		  @ decreases	keys[i].length - j;
		  @*/
		for (int j = 0; j < keys[i].length; j++) {
			if (keys[i][j].equals(key)) {
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
	/*@
	  @ public normal_behavior
	  @   requires	true;
	  @
	  @   //The result is not null if and only if the given key is in the hash table 
	  @   //	and the result is the Value at the same postion.
	  @	  //	getIndex needs to ensure, that the key is in the table or not?
	  @	  //	We could use getIndex or a new contains to obscure the data layout.
	  @   ensures	(\result != null) <==> 
	  @					(\exists int x; 0 <= x && x < chains;
	  @						(\exists int y; 0 <= y && y < vals[x].length;
	  @							vals[x][y] == \result));
	  @
	  @	  //We already know that no value can be null (invariant), so we need a diffrent
	  @	  //	if the result is null.
	  @
	  @   assignable	\nothing;
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

		int i = hash(key);
		int j = getIndex(i, key);

		if (j != -1) {
			return vals[i][j];
		}

		return null;
	}
	
	//RunTimeExceptions
	//IndexOutOfBoundsException - if copying would cause access of data outside array bounds.
	//NullPointerException - if either src or dest is null.
	/*@
	  @ public normal_behavior
	  @   requires	keysTemp.length == valsTemp.length;
	  @	  requires	0 <= i && i < chains;
	  @   requires	0 <= srcPos && srcPos < keys[i].length;
	  @   requires	0 <= destPos && destPos < keysTemp.length;
	  @   requires	0 <= length && length + srcPos <= keys[i].length 
	  @				&& length + destPos <= keysTemp.length;
	  @   ensures	(\forall int x; 0 <= x && x < length; 
	  @					keysTemp[destPos + x] == keys[i][srcPos + x] 
	  @					&& valsTemp[destPos + x] == vals[i][srcPos + x]);
	  @   assignable	valsTemp[*], keysTemp[*];
	  @*/
	private void arrayCopy(HashObject[] keysTemp, Object[] valsTemp, int i ,int srcPos, int destPos, int length) {
		/*@ //The arrays are a copys of the other arrays up until this point.
		  @ loop_invariant	0 <= k && k <= length &&
		  @					(\forall int x; 0 <= x && x < k; 
		  @						keysTemp[destPos + x] == keys[i][srcPos + x] 
		  @						&& valsTemp[destPos + x] == vals[i][srcPos + x]);
		  @ assignable valsTemp[*], keysTemp[*];
		  @ decreases length - k;
		  @*/
		for (int k = 0; k < length; k++) {
			keysTemp[destPos + k] = keys[i][srcPos + k];
			valsTemp[destPos + k] = vals[i][srcPos + k];
		}
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
	  @   //The given key is now exactly ones in the hash table.
	  @   ensures	(\exists int x; 0 <= x && x < keys[hash(key)].length; 
	  @					keys[hash(key)][x].equals(key)
	  @					&& (\forall int y; 0 <= y && y <= keys[hash(key)].length;
	  @						keys[hash(key)][y].equals(key) ==> (x == y)));
	  @   
	  @   //The amount of elements in the hash table (called n) is now either n or n+1.
	  @   ensures	((n == \old(n)) <=!=> (n == \old(n) + 1));
	  @   
	  @   //If n is now n, then the key was and still is in the table and the given value is at this postion.
	  @   //	The current contract might not hold if resize is used, 
	  @   //	since the contract requires that the keys postion did not change.
	  @   ensures	(n == \old(n)) ==>
	  @					(\exists int x; 0 <= x && x < keys[hash(key)].length;
	  @						keys[hash(key)][x].equals(key) && \old(keys[hash(key)][x].equals(key))
	  @						&& vals[hash(key)][x] == val);
	  @   
	  @   //If n is now n+1, then the table size at the keys postion (hash(key)) did increase by 1 and
	  @   //	the key-value-pair is now at the new postion. (Duplicate was already checked)
	  @   ensures	(n == \old(n) + 1) ==>
	  @					((keys[hash(key)].length == \old(keys[hash(key)].length) + 1) 
	  @						&& keys[hash(key)][keys[hash(key)].length-1].equals(key)
	  @						&& vals[hash(key)][vals[hash(key)].length-1] == val);
	  @
	  @   assignable	keys[*], vals[*], vals[hash(key)][*], n;
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

		// double table size if 50% full
		// if (n >= (len * m / 2))
		// resize(2 * m, len);

		int i = hash(key);
		int j = getIndex(i, key);

		if (j != -1) {
			vals[i][j] = val;
			return;
		}

		HashObject[] keysTemp = new HashObject[keys[i].length + 1];
		Object[] valsTemp = new Object[vals[i].length + 1];
		
		arrayCopy(keysTemp, valsTemp, i, 0, 0, keys[i].length);

		keysTemp[keys[i].length] = key;
		valsTemp[vals[i].length] = val;

		keys[i] = keysTemp;
		vals[i] = valsTemp;
		n++;
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
	  @   ensures (n == \old(n)) <=!=> (n == \old(n) - 1);
	  @
	  @   //If n is now n-1, then the key was in the hash table at the start of the method and
	  @   //	the table size at the keys postion did decrease be 1.
	  @   ensures (n == \old(n) - 1) ==> 
	  @			   ((\exists int x; 0 <= x && x <= \old(keys[hash(key)].length);
	  @				   \old(keys[hash(key)][x].equals(key)))
	  @			   && (keys[hash(key)].length == \old(keys[hash(key)].length) - 1));
	  @   assignable keys[*], vals[*], n;
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

		int i = hash(key);
		int d = getIndex(i, key);

		if (d >= 0) {
			HashObject[] keysTemp = new HashObject[keys[i].length - 1];
			Object[] valsTemp = new Object[vals[i].length - 1];
			
			arrayCopy(keysTemp, valsTemp, i, 0, 0, d);
			arrayCopy(keysTemp, valsTemp, i, d + 1, d, keys[i].length - d - 1);

			keys[i] = keysTemp;
			vals[i] = valsTemp;
			n--;
		}

		// halves size of array if it's 12.5% full or less
		// if (m > INIT_CAPACITY && n <= len * m / 8)
		// resize(m / 2, len);
	}

	/**
	 * The maximum size of array to allocate. Some VMs reserve some header words in
	 * an array. Attempts to allocate larger arrays may result in OutOfMemoryError:
	 * Requested array size exceeds VM limit
	 */
	private static final int MAX_ARRAY_SIZE = Integer.MAX_VALUE - 8;

	// resize the hash table to have the given number of chains
	// rehashing all of the keys
	/*@ public normal_behavior
	  @   requires true;
	  @
	  @   //The amount of entrys in the hash table did not change.
	  @   ensures \old(n) == n;
	  @
	  @   //Every entry of the old hash table is in the new table.
	  @   ensures (\forall int x; 0 <= x && x < \old(keys.length);
	  @			   (\forall int y; 0 <= y && y < \old(keys[x].length);
	  @				   \old(get(keys[x][y])) == get(\old(keys[x][y]))));
	  @   assignable n, chains, keys, vals;
	  @*/
	private void resize(int chains) {
		if (chains > MAX_ARRAY_SIZE)
			chains = MAX_ARRAY_SIZE;
		if (chains < 1)
			chains = 1;

		SeparateChainingArray temp = new SeparateChainingArray(chains);

		/*@ //Every entry of every chain up until now is in the new table.
		  @ //The amount of transferd entrys is equal to the amount of entrys in the new table.
		  @ loop_invariant 0 <= i && i <= keys.length
		  @				&& (\forall int x; 0 <= x && x < i;
		  @					(\forall int y; 0 <= y && y < keys[i].length;
		  @						(get(keys[x][y]) == temp.get(keys[x][y]))))
		  @				&& (\sum int x; 0 <= x && x < i; keys[i].length)
		  @					== temp.n;
		  @ assignable temp.*;
		  @ decreases keys.length - i;
		  @*/
		for (int i = 0; i < keys.length; i++) {
			/*@ //Every entry of the current chain up until now is in the new table.
			  @ //The amount of transferd entrys is equal to the amount of entrys in the new table.
			  @ loop_invariant 0 <= j && j <= keys[i].length &&
			  @				(\forall int x; 0 <= x && x < j;
			  @					 (get(keys[i][x]) == temp.get(keys[i][x])))
			  @				&& ((\sum int x; 0 <= x && x < i; keys[i].length) + j)
			  @					== temp.n;
			  @ assignable temp.*;
			  @ decreases keys[i].length - j;
			  @*/
			for (int j = 0; j < keys[i].length; j++) {
				temp.put(keys[i][j], vals[i][j]);
			}
		}
		this.n = temp.n; // Should not change, further investigation needed
		this.chains = temp.chains;
		this.keys = temp.keys;
		this.vals = temp.vals;
	}

	// hash function for keys - returns value between 0 and chains-1
	/*@ public normal_behavior
	  @   requires	true;
	  @   ensures	(\forall HashObject o; o.equals(key) 
	  @					==> (\result == (abs(o.hashCode()) % chains)))
	  @				&& 0 <= \result && \result < chains;
	  @*/
	private /*@ strictly_pure @*/ int hash(HashObject key) {
		return abs(key.hashCode()) % chains;
	}

	/**
	 * @return the number of key-value pairs in this hash table
	 */
	public int size() {
		return n;
	}

	/**
	 * Returns true if this hash table is empty.
	 */
	public boolean isEmpty() {
		return size() == 0;
	}

	private int abs(int number) {
		if (number == Integer.MIN_VALUE)
			return 0;
		if (number < 0)
			return -number;
		return number;
	}

	/**
	 * Returns true if this hash table contains the specified key.
	 *
	 * @param key
	 *            the key
	 * @return true if this hash table contains key; false otherwise
	 * @throws IllegalArgumentException
	 *             if key is null
	 */
	public boolean contains(HashObject key) {
		if (key == null)
			throw new IllegalArgumentException("argument to contains() is null");
		return get(key) != null;
	}
}

public class HashObject {

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

	public /*@ strictly_pure @*/ boolean equals(/*@ nullable @*/ Object otherObject) {
		if (!(otherObject instanceof HashObject))
			return false;
		return this.value == ((HashObject) otherObject).getValue();
	}
}