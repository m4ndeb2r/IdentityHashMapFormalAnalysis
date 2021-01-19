/**
 * This implementation uses a separate chaining with arrays as collision
 * resolution strategy. It supports the usual put, get, contains, delete, size
 * and is-empty methods. When associating a value with a key that is already in
 * the hash table, the convention is to replace the old value with the new
 * value.
 */
public class SeparateChainingArrayHash {

	private static final int INIT_CAPACITY = 8;

	private int n;                  // number of key-value pairs
	private int chains;             // hash table size
	private HashObject[][] keys;    // two dimensional array for keys
	private Object[][] vals;        // two dimensional array for keys
    
    //This comment roughly describes what the invariant is supposed to mean.
    //- The arrays keys and vals are equally long.
    //- Each array inside of keys has an equally long partner array in vals at the same postion. 
    /*@ instance invariant keys.length == vals.length && chains == keys.length
      @                    && (\forall int x; 0 <= x && x < chains;
      @                        keys[x].length == vals[x].length);
      @*/

	/**
	 * Initializes an empty symbol table.
	 */
	public SeparateChainingArrayHash() {
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
	public SeparateChainingArrayHash(int chains) {
		if (chains <= 0)
			throw new IllegalArgumentException("Chains needs to be at least 1");
		n = 0;
		this.chains = chains;
		keys = new HashObject[chains][0];
		vals = new Object[chains][0];
	}

	/**
	 * Returns the value associated with the specified key in this hash table.
	 *
	 * @param key the key
	 * @return the value associated with key in the hash table; null if no such value
	 * @throws IllegalArgumentException if key is null
	 */
    //This comment roughly describes what the ensures clause is supposed to mean.
    //- The result is null if and only if the given key is not in the hash table.
    //- The result is not null if and only if the given key is in the hash table 
    //    and the result is the Value at the same postion.
	/*@
	  @ public normal_behavior
      @   requires key != null;
	  @   ensures (\result == null <==>
      @               (\forall int x; 0 <= x && x < keys[hash(key)].length; 
      @                   !(keys[hash(key)][x].equals(key))))
      @           && (\result != null <==> 
      @               (\exists int y; 0 <= y && y < keys[hash(key)].length;
      @                   keys[hash(key)][y].equals(key) && vals[hash(key)][y] == \result));
      @   assignable \nothing;
      @
      @ also
      @ exceptional_behavior
      @   requires key == null;
      @   signals_only IllegalArgumentException;
      @   signals (IllegalArgumentException e) true;
	  @*/
	public /*@ pure @*/ Object get(HashObject key) {
		if (key == null) throw new IllegalArgumentException("argument to get() is null");
            
        int i = hash(key);

        //This comment roughly describes what the loop_invariant is supposed to mean.
        //- Every postion in the array up until now didnt include the key.
        //    This is always true, since the method terminates if the key is found.
		/*@ loop_invariant 0 <= j && j <= keys[i].length &&
          @                (\forall int x; 0 <= x && x < j; !(keys[i][x].equals(key)));
		  @ assignable \strictly_nothing;
		  @ decreases keys[i].length - j;
		  @*/
		for (int j = 0; j < keys[i].length; j++) {
			if (keys[i][j].equals(key)) {
				return vals[i][j];
			}
		}
		return null;
	}

	/**
	 * Inserts the specified key-value pair into the hash table, overwriting the old
	 * value with the new value if the hash table already contains the specified
	 * key. Sets the occupied flag to false (and therefore delete) the specified key
	 * (and its associated value) from this hash table if the specified value is
	 * null.
	 *
	 * @param key the key
	 * @param val the value
	 * @throws IllegalArgumentException if key or val is null
	 */
    //This comment roughly describes what the ensures clause is supposed to mean.
    //- The given key is now exactly ones in the hash table.
    //- The amount of elements in the hash table (called n) is now either n or n+1.
    //- If n is now n, then the key was and still is in the table and the given value is at this postion.
    //    The current contract might not hold if resize is used, 
    //    since the contract requires that the keys postion did not change.
    //- If n is now n+1, then the table size at the keys postion (hash(key)) did increase by 1 and
    //    the key-value-pair is now at the new postion. (Duplicate was already checked)
	/*@ public normal_behavior
      @   requires key != null && val != null;
      @   ensures (\exists int x; 0 <= x && x < keys[hash(key)].length; 
      @                   keys[hash(key)][x].equals(key)
      @                   && (\forall int y; 0 <= y && y <= keys[hash(key)].length;
      @                          keys[hash(key)][y].equals(key) ==> (x == y)))
      @           && ((n == \old(n)) <=!=> (n == \old(n) + 1))
      @           && (n == \old(n)) ==>
      @               (\exists int x; 0 <= x && x < keys[hash(key)].length;
      @                   keys[hash(key)][x].equals(key) && \old(keys[hash(key)][x].equals(key))
      @                   && vals[hash(key)][x] == val)
      @           && (n == \old(n) + 1) ==>
      @               ((keys[hash(key)].length == \old(keys[hash(key)].length) + 1) 
      @                   && keys[hash(key)][keys[hash(key)].length-1].equals(key)
      @                   && vals[hash(key)][vals[hash(key)].length-1] == val);
      @   assignable keys[*], vals[*], vals[hash(key)][*], n;
      @
      @ also
      @ exceptional_behavior
      @   requires key == null || val == null;
      @   signals_only IllegalArgumentException;
      @   signals (IllegalArgumentException e) true;
	  @*/
	public void put(HashObject key, Object val) {
		if (key == null)
			throw new IllegalArgumentException("first argument to put() is null");
        if (val == null)
			throw new IllegalArgumentException("second argument to put() is null");

		// double table size if 50% full
		//if (n >= (len * m / 2))
        //    resize(2 * m, len);

		int i = hash(key);

		// So a key can't be twice in the hash table
        //This comment roughly describes what the loop_invariant is supposed to mean.
        //- Every postion in the array up until now didnt include the key.
        //    This is always true, since the method terminates if the key is found and 
        //    the new value is written.
		/*@ loop_invariant 0 <= j && j <= keys[i].length &&
          @                (\forall int x; 0 <= x && x < j; !(keys[i][x].equals(key)));
          @ assignable vals[i][*];
          @ decreases keys[i].length - j;
		  @*/
		for (int j = 0; j < keys[i].length; j++) {
			if (keys[i][j].equals(key)) {
				vals[i][j] = val;
				return;
			}
		}

		HashObject[] keysTemp = new HashObject[keys[i].length+1];
        Object[] valsTemp = new Object[vals[i].length+1];
        
        //This comment roughly describes what the loop_invariant is supposed to mean.
        //- The arrays are a copys of the other arrays up until this point.
        /*@ loop_invariant 0 <= k && k <= keys[i].length &&
          @                (\forall int x; 0 <= x && x < k; 
          @                    keysTemp[x] == keys[i][x] && valsTemp[x] == vals[i][x]);
          @ assignable valsTemp[*], keysTemp[*];
          @ decreases keys[i].length - k;
		  @*/
        for (int k = 0; k < keys[i].length; k++) {
            keysTemp[k] = keys[i][k];
            valsTemp[k] = vals[i][k];
        }
        
        keysTemp[keys[i].length+1] = key;
        valsTemp[vals[i].length+1] = val;
        
        keys[i] = keysTemp;
        vals[i] = valsTemp;
		n++;
	}

	/**
	 * Removes the specified key and its associated value from this hash table (if
	 * the key is in this hash table).
	 *
	 * @param key the key
	 * @throws IllegalArgumentException if key is null
	 */
    //This comment roughly describes what the ensures clause is supposed to mean.
    //- The given key is not in the table. (This can already be true at the beginning)
    //- The amount of elements in the hash table (called n) is now either n or n-1.
    //- If n is now n-1, then the key was in the hash table at the start of the method and
    //    the table size at the keys postion did decrease be 1.
	/*@
	  @ public normal_behavior
      @   requires key != null;
      @   ensures (\forall int x; 0 <= x && x <= keys[hash(key)].length;
      @               !(keys[hash(key)][x].equals(key)))
      @           && ((n == \old(n)) <=!=> (n == \old(n) - 1))
      @           && (n == \old(n) - 1) ==> 
      @               ((\exists int x; 0 <= x && x <= \old(keys[hash(key)].length);
      @                   \old(keys[hash(key)][x].equals(key)))
      @               && (keys[hash(key)].length == \old(keys[hash(key)].length) - 1));
      @   assignable keys[*], vals[*], n;
      @
      @ also
      @ exceptional_behavior
      @   requires key == null;
      @   signals_only IllegalArgumentException;
      @   signals (IllegalArgumentException e) true;
	  @*/
	public void delete(HashObject key) {
		if (key == null) throw new IllegalArgumentException("argument to delete() is null");

		int i = hash(key);
        int d = -1;

        //This comment roughly describes what the loop_invariant is supposed to mean.
        //- Every postion in the array up until now, that is not d, didnt include the key.
        //- If d is at least 0, then the given key is at this postion.
		/*@ loop_invariant 0 <= j && j <= keys[i].length 
          @                && ((\forall int x; 0 <= x && x < j && x != d; !(keys[i][x].equals(key))))
          @                && (d >= 0) ==> (keys[i][d].equals(key));
          @ assignable d;
          @ decreases keys[i].length - j;
		  @*/
		for (int j = 0; j < keys[i].length; j++) {
			if (keys[i][j].equals(key)) {
				d = j;
			}
		}
        
        if (d >= 0) {
            HashObject[] keysTemp = new HashObject[keys[i].length-1];
            Object[] valsTemp = new Object[vals[i].length-1];
            
            //This comment roughly describes what the loop_invariant is supposed to mean.
            //- The arrays are a copys of the other arrays up until this point.
            /*@ loop_invariant 0 <= k && k <= d &&
              @                (\forall int x; 0 <= x && x < k; 
              @                    keysTemp[x] == keys[i][x] && valsTemp[x] == vals[i][x]);
              @ assignable valsTemp[*], keysTemp[*];
              @ decreases d - k;
              @*/
            for (int k = 0; k < d; k++) {
                keysTemp[k] = keys[i][k];
                valsTemp[k] = vals[i][k];
            }
            
            //This comment roughly describes what the loop_invariant is supposed to mean.
            //- The arrays are a copys of the other arrays starting from d+1 up until this point, 
            //    but moved one index lower.
            /*@ loop_invariant d+1 <= k && k <= keys[i].length &&
              @                (\forall int x; d+1 <= x && x < k; 
              @                    keysTemp[x] == keys[i][x] && valsTemp[x] == vals[i][x]);
              @ assignable valsTemp[*], keysTemp[*];
              @ decreases keys[i].length - k;
              @*/
            for (int l = d+1; l < keys[i].length; l++) {
                keysTemp[l-1] = keys[i][l];
                valsTemp[l-1] = vals[i][l];
            }
        
            keys[i] = keysTemp;
            vals[i] = valsTemp;
            n--;
        }

		// halves size of array if it's 12.5% full or less
		//if (m > INIT_CAPACITY && n <= len * m / 8)
			//resize(m / 2, len);
	}
    
    /**
	 * The maximum size of array to allocate. Some VMs reserve some header words in
	 * an array. Attempts to allocate larger arrays may result in OutOfMemoryError:
	 * Requested array size exceeds VM limit
	 */
	private static final int MAX_ARRAY_SIZE = Integer.MAX_VALUE - 8;

	// resize the hash table to have the given number of chains
	// rehashing all of the keys
    //This comment roughly describes what the ensures clause is supposed to mean.
    //- The amount of entrys in the hash table did not change.
    //- Every entry of the old hash table is in the new table.
    /*@ public normal_behavior
      @   requires true;
	  @   ensures \old(n) == n
      @           && (\forall int x; 0 <= x && x < \old(keys.length);
      @               (\forall int y; 0 <= y && y < \old(keys[x].length);
      @                   \old(get(keys[x][y])) == get(\old(keys[x][y]))));
      @   assignable n, chains, keys, vals;
	  @*/
	private void resize(int chains) {
		if (chains > MAX_ARRAY_SIZE)
			chains = MAX_ARRAY_SIZE;
		if (chains < 1)
			chains = 1;

		SeparateChainingArrayHash temp = new SeparateChainingArrayHash(chains);
        
        //This comment roughly describes what the loop_invariant is supposed to mean.
        //- Every entry of every chain up until now is in the new table.
        //- The amount of transferd entrys is equal to the amount of entrys in the new table.
        /*@ loop_invariant 0 <= i && i <= keys.length
          @                && (\forall int x; 0 <= x && x < i;
          @                    (\forall int y; 0 <= y && y < keys[i].length;
          @                        (get(keys[x][y]) == temp.get(keys[x][y]))))
          @                && (\sum int x; 0 <= x && x < i; keys[i].length)
          @                    == temp.n;
		  @ assignable temp;
		  @ decreases keys.length - i;
		  @*/
		for (int i = 0; i < keys.length; i++) {
            //This comment roughly describes what the loop_invariant is supposed to mean.
            //- Every entry of the current chain up until now is in the new table.
            //- The amount of transferd entrys is equal to the amount of entrys in the new table.
            /*@ loop_invariant 0 <= j && j <= keys[i].length &&
              @                (\forall int x; 0 <= x && x < j;
              @                     (get(keys[i][x]) == temp.get(keys[i][x])))
              @                && ((\sum int x; 0 <= x && x < i; keys[i].length) + j)
              @                    == temp.n;
		      @ assignable temp;
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
	private /*@ strictly_pure @*/ int hash(HashObject key) {
		return (key.hashCode() & 0x7fffffff) % chains;
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

	/**
	 * Returns true if this hash table contains the specified key.
	 *
	 * @param key the key
	 * @return true if this hash table contains key; false otherwise
	 * @throws IllegalArgumentException if key is null
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
	
	public /*@ strictly_pure @*/ int getValue() {
		return value;
	}
	
	public /*@ strictly_pure @*/ int hashCode() {
		return value;
	}
	
	public /*@ strictly_pure @*/ boolean equals(Object otherObject) {
		if (otherObject == this) return true;
		if (otherObject == null || !(otherObject instanceof HashObject)) return false;
		return this.value == ((HashObject) otherObject).getValue();
	}
}