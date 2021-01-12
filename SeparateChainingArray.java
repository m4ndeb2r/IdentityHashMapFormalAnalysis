/**
 *  This implementation uses a separate chaining with arrays as collision resolution strategy.
 *  It supports the usual put, get, contains, delete, size and is-empty methods.
 *  When associating a value with a key that is already in the hash table,
 *  the convention is to replace the old value with the new value.
 */
public class SeparateChainingArrayHash {
    private static class Entry { // table entry
        Integer key;
        Integer value;
        boolean occupied;
    }
    
    private static final int INIT_CAPACITY = 8;

    private int n;                                // number of key-value pairs
    private int m;                                // hash table size
    private int len;                              // entry array length
    private Entry[][] table;                      // array of entry arrays
    
    /**
     * Initializes an empty symbol table.
     */
    public SeparateChainingArrayHash() {
        this(INIT_CAPACITY, INIT_CAPACITY);
    }
    
    /**
     * Initializes an empty hash table with m chains each with a size of 8.
     * @param m the initial number of chains
     */
    public SeparateChainingArrayHash(int m) {
        this(m, INIT_CAPACITY);
    }
    
    /**
     * Initializes an empty hash table with m chains each with a size of len.
     * @param chains the initial number of chains, needs to be at least 1.
     * @param length the length of the entry arrays, needs to be at least 1.
     *          should not be to big, because of slow down 
     *          (entry array is searched linear)
     * @throws IllegalArgumentException if chains or length is smaller then 1
     */
    public SeparateChainingArrayHash(int chains, int length) {   //<Key, Value>?
        if (chains <= 0) throw new IllegalArgumentException("Chains needs to be at least 1");
        if (length <= 0) throw new IllegalArgumentException("Length needs to be at least 1");
        n = 0;
        this.m = chains;
        this.len = length;
        table = (Entry[][]) new Entry[chains][length];
        for (int i = 0; i < table.length; i++) {
            for (int j = 0; j < table[i].length; j++) {
                table[i][j] = new Entry();
                table[i][j].occupied = false;
            }
        }
    }
    
    /**
     * The maximum size of array to allocate.
     * Some VMs reserve some header words in an array.
     * Attempts to allocate larger arrays may result in
     * OutOfMemoryError: Requested array size exceeds VM limit
     */
    private static final int MAX_ARRAY_SIZE = Integer.MAX_VALUE - 8;
    
    // resize the hash table to have the given number of chains and length
    // rehashing all of the keys
    // possible memory overflow
    /*@ public normal_behavior
      @   requires chains >= 0 && length >= 0;
	  @   ensures \old(n) == n &&
      @           (\forall int x; 0 <= x && x < m;
      @               (\forall int y; 0 <= y && y < table[x].length && table[x][y].occupied == true;
      @                   (get(table[x][y].key) == \old(this.get(table[x][y].key)))));
      @   assignable n, m, len, table;
	  @*/
    private void resize(int chains, int length) {
        if (chains * length > MAX_ARRAY_SIZE) chains = MAX_ARRAY_SIZE / length;
        if (chains < 1) chains = 1;
        if (length < 1) length = 1;
        
        SeparateChainingArrayHash temp 
                = new SeparateChainingArrayHash(chains, length);
        
        /*@ loop_invariant 0 <= i && i <= table.length
          @                && (\forall int x; 0 <= x && x < i;
          @                    (\forall int y; 0 <= y && y < table[i].length && table[x][y].occupied == true;
          @                        (get(table[x][y].key) == temp.get(table[x][y].key))))
          @                && (\sum int x; 0 <= x && x < i;
          @                    (\num_of int y; 0 <= y && y < table[i].length && table[x][y].occupied == true))
          @                    == temp.n;
		  @ assignable temp.table, n;
		  @ decreases table.length - i;
		  @*/
        for (int i = 0; i < table.length; i++) {
            //An entry can have a new index in the first array, so testing for n is difficult.
            /*@ loop_invariant 0 <= j && j <= table[i].length &&
              @                (\forall int x; 0 <= x && x < j && table[i][x].occupied == true;
              @                     (get(table[i][x].key) == temp.get(table[i][x].key)));
		      @ assignable temp.table[i][*], n;
		      @ decreases table[i].length - j;
		      @*/
            for (int j = 0; j < table[i].length; j++) {
                if (table[i][j].occupied == true) {
                    //It is possible that resize is called.
                    temp.put(table[i][j].key, table[i][j].value);
                }
            }
        }
        this.n = temp.n;            //Should not change, further investigation needed
        this.m = temp.m;            
        this.len = temp.len;        
        this.table = temp.table;    //Is this covered by table[*][*]?
    }
    
    // hash function for keys - returns value between 0 and m-1
    private /*@ pure @*/ int hash(Integer key) {
        return (key.hashCode() & 0x7fffffff) % m;
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
     * @param  key the key
     * @return true if this hash table contains key;
     *         false otherwise
     * @throws IllegalArgumentException if key is null
     */
    public boolean contains(Integer key) {
        if (key == null) throw new IllegalArgumentException("argument to contains() is null");
        return get(key) != null;
    } 
    
    /**
     * Returns the value associated with the specified key in this hash table.
     *
     * @param  key the key
     * @return the value associated with key in the hash table;
     *         null if no such value
     * @throws IllegalArgumentException if key is null
     */
    /*@
	  @ public normal_behavior
      @   requires key != null;
	  @   ensures (\result == null && 
      @           (\forall int x; 0 <= x && x < table[hash(key)].length; 
      @               table[hash(key)][x].occupied == false || table[hash(key)][x].key != key))
      @           || (\exists int y; 0 <= y && y < table[hash(key)].length;
      @               table[hash(key)][y].occupied == true && table[hash(key)][y].key == key
      @               && table[hash(key)][y].value == \result);
      @   assignable \nothing;
      @
      @ also
      @ exceptional_behavior
      @   requires key == null;
      @   signals_only IllegalArgumentException;
      @   signals (IllegalArgumentException e) true;
	  @*/
    public /*@ pure @*/ Integer get(Integer key) {
        if (key == null) throw new IllegalArgumentException("argument to get() is null");
        int i = hash(key);
        
        /*@ loop_invariant 0 <= j && j <= table[i].length &&
          @                (\forall int x; 0 <= x && x < j; 
          @                     table[i][x].occupied == false || table[i][x].key != key);
		  @ assignable \strictly_nothing;
		  @ decreases table[i].length - j;
		  @*/
        for (int j = 0; j < table[i].length; j++) {
            if (table[i][j].occupied == true && table[i][j].key == key) {
                return table[i][j].value;
            }
        }
        return null;
    }
    
    /**
     * Inserts the specified key-value pair into the hash table, overwriting the old 
     * value with the new value if the hash table already contains the specified key.
     * Sets the occupied flag to false (and therefore delete) the specified key (and 
     * its associated value) from this hash table if the specified value is null.
     *
     * @param  key the key
     * @param  val the value
     * @throws IllegalArgumentException if key or val is null
     */
    /*@ public normal_behavior
      @   requires key != null && val != null;
	  @   ensures (n == \old(n) || n == \old(n) + 1)
      @           && (\old(n) >= (\old(len) * \old(m) / 2)) ==> (m == \old(m) * 2)
      @           && (\old(n) == n) ==>
      @               (\exists int x; 0 <= x && x < table[hash(key)].length;
      @                   \old(table[hash(key)][x].occupied) == true && \old(table[hash(key)][x].key) == key
      @                   && table[hash(key)][x].occupied == true && table[hash(key)][x].key == key
      @                   && table[hash(key)][x].value == val)
      @           && (\old(n) + 1 == n) ==> 
      @               (((\exists int y; 0 <= y && y < \old(len);
      @                   \old(table[hash(key)][y].occupied) == false)
      @               || \old(len) * 2 == len)
      @               && (\exists int z; 0 <= z && z <= table[hash(key)].length;
      @                   table[hash(key)][z].occupied == true && table[hash(key)][z].key == key 
      @                   && table[hash(key)][z].value == val))
      @           && (\exists int x; 0 <= x && x <= table[hash(key)].length;
      @                   table[hash(key)][x].occupied == true && table[hash(key)][x].key == key
      @                   && (\forall int y; 0 <= y && y <= table[hash(key)].length;
      @                          (table[hash(key)][y].occupied == true && table[hash(key)][y].key == key)
      @                          ==> (x == y)));
      @   assignable n, m, len, table;
      @
      @ also
      @ exceptional_behavior
      @   requires key == null || val == null;
      @   signals_only IllegalArgumentException;
      @   signals (IllegalArgumentException e) true;
	  @*/ 
    public void put(Integer key, Integer val) {
        if (key == null) throw new IllegalArgumentException("first argument to put() is null");
        if (val == null) throw new IllegalArgumentException("second argument to put() is null");

        // double table size if 50% full
        if (n >= (len * m / 2)) {
            resize(2*m, len);
        }

        int i = hash(key);

        // So a key can't be twice in the hash table
        /*@ loop_invariant 0 <= j && j <= table[i].length &&
          @                (\forall int x; 0 <= x && x < j; 
          @                     table[i][x].occupied == false || table[i][x].key != key);
		  @ assignable table[i][*];
		  @ decreases table[i].length - j;
		  @*/
        for (int j = 0; j < table[i].length; j++) {
            if (table[i][j].occupied == true && table[i][j].key == key) {
                table[i][j].value = val;
                return;
            }
        }
        
        /*@ loop_invariant 0 <= k && k <= table[i].length &&
          @                (\forall int x; 0 <= x && x < k; table[i][x].occupied == true);
          @ assignable table[i][*], n;
          @ decreases table[i].length - k;
		  @*/
        for (int k = 0; k < table[i].length; k++) {
            if (table[i][k].occupied == false) {
                table[i][k].key = key;
                table[i][k].value = val;
                table[i][k].occupied = true;
                n++;
                return;
            }
        }
        
        resize(m, len*2);
        table[i][len/2].key = key;
        table[i][len/2].value = val;
        table[i][len/2].occupied = true;
        n++;
    }

    /**
     * Removes the specified key and its associated value from this hash table     
     * (if the key is in this hash table).    
     *
     * @param  key the key
     * @throws IllegalArgumentException if key is null
     */
    /*@
	  @ public normal_behavior
      @   requires key != null;
	  @   ensures (n == \old(n) || n == \old(n) - 1)
      @           && (\old(n) == n) ==>
      @               (\forall int x; 0 <= x && x < table[hash(key)].length; 
      @                   table[hash(key)][x].occupied == false || table[hash(key)][x].key != key)
      @           && (\old(n) - 1 == n) ==>
      @               ((\old(m) > INIT_CAPACITY && n <= len * \old(m) / 8) 
      @                   ==> (m == \old(m) / 2)
      @               && (\exists int x; 0 <= x && x < table[hash(key)].length;
      @                   \old(table[hash(key)][x].occupied) == true && table[hash(key)][x].key == key
      @                   && table[hash(key)][x].occupied == false));
      @   assignable n, table;
      @
      @ also
      @ exceptional_behavior
      @   requires key == null;
      @   signals_only IllegalArgumentException;
      @   signals (IllegalArgumentException e) true;
	  @*/
    public void delete(Integer key) {
        if (key == null) throw new IllegalArgumentException("argument to delete() is null");

        int i = hash(key);
        
        /*@ loop_invariant 0 <= j && j <= table[i].length && (n == \old(n) || n == \old(n) - 1)
          @                && (\old(n) - 1 == n) ==>
          @                    (\exists int x; 0 <= x && x < j;
          @                        \old(table[i][x].occupied) == true && table[i][x].key == key
          @                        && table[i][x].occupied == false)
          @                && (\old(n) == n) ==>
          @                    (\forall int x; 0 <= x && x < j; 
          @                        table[i][x].occupied == false || table[i][x].key != key);
		  @ assignable n, table[i][*];
		  @ decreases table[i].length - j;
		  @*/
        for (int j = 0; j < table[i].length; j++) {
            if (table[i][j].occupied == true && table[i][j].key == key) {
                table[i][j].occupied = false;
                n--;
            }
        }

        // halves size of array if it's 12.5% full or less
        if (m > INIT_CAPACITY && n <= len * m / 8) resize(m/2, len);
    } 
}