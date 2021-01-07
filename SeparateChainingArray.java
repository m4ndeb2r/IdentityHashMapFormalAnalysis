public class SeparateChainingArrayHash<Key, Value> {
    private static class Entry<K, V> { // table entry
        K key;
        V value;
        boolean occupied;
    }
    
    private static final int INIT_CAPACITY = 8;

    private int n;                                // number of key-value pairs
    private int m;                                // hash table size
    private int l;                                // entry array length
    private Entry<Key, Value>[][] table;          // array of entry arrays
    
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
     * Initializes an empty hash table with m chains each with a size of l.
     * @param m the initial number of chains
     * @param l the length of the entry arrays
     *          should not be to big, because of slow down 
     *          (entry array is searched linear)
     */
    public SeparateChainingArrayHash(int m, int l) {
        n = 0;
        this.m = m;
        this.l = l;
        table = (Entry<Key, Value>[][]) new Entry[m][l];
        for (int i = 0; i < table.length; i++) {
            for (int j = 0; j < table[i].length; j++) {
                table[i][j] = new Entry<>();
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
    
    // resize the hash table to have the given number of chains,
    // rehashing all of the keys
    private void resize(int chains) {
        if (chains > MAX_ARRAY_SIZE) {
            return;
        }
        
        SeparateChainingArrayHash<Key, Value> temp 
                = new SeparateChainingArrayHash<Key, Value>(chains, l);
        for (int i = 0; i < table.length; i++) {
            for (int j = 0; j < table[i].length; j++) {
                if (table[i][j].occupied == true) {
                    temp.put(table[i][j].key, table[i][j].value);
                }
            }
        }
        this.n = temp.n;
        this.m = temp.m;
        this.l = temp.l;
        this.table = temp.table;
    }
    
    // hash function for keys - returns value between 0 and m-1
    // "& 0x7fffffff" : turn the 32-bit integer into a 31-bit nonnegative integer
    private int hash(Key key) {
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
    public boolean contains(Key key) {
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
	  @ public normal_behaviour
      @   requires key != null;
	  @   ensures \result == null && (\forall int x; 0 <= x && x < table[i].length; 
      @               table[i][x].occupied == false || table[i][x].key != key) ||
      @           (\exists int y; 0 <= y && y < table[i].length;
      @               table[i][y].occupied == true && table[i][y].key == key &&
      @               table[i][y].value == \result);
      @   assignable \nothing;
	  @*/
    public Value get(Key key) {
        if (key == null) throw new IllegalArgumentException("argument to get() is null");
        int i = hash(key);
        
        /*@
		  @ loop_invariant 0 <= j && j <= table[i].length &&
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
     * @throws IllegalArgumentException if key is null
     */
    public void put(Key key, Value val) {
        if (key == null) throw new IllegalArgumentException("first argument to put() is null");
        if (val == null) {
            delete(key);
            return;
        }

        // double table size if 50% full
        if (n >= (l * m * / 2)) {
            resize(2*m);
        }

        int i = hash(key);

        // So a key cant be twice in the hash table
        for (int j = 0; j < table[i].length; j++) {
            if (table[i][j].occupied == true && table[i][j].key == key) {
                table[i][j].value = val;
                return;
            }
        }
        
        //possible memory overflow
        //limit the while loop and return error that the element could not be put
        // Or increase the entry array size, inefficent but easy
        boolean b = true;
        while (b) {
            for (int j = 0; j < table[i].length; j++) {
                if (table[i][j].occupied == false) {
                    table[i][j].key = key;
                    table[i][j].value = val;
                    table[i][j].occupied = true;
                    n++;
                    return;
                }
            }
            if (m*2 <= MAX_ARRAY_SIZE) {
                resize(2*m);
                i = hash(key);
            } else {
                b = false;
                // was dann?
            }
        }
    }

    /**
     * Removes the specified key and its associated value from this hash table     
     * (if the key is in this hash table).    
     *
     * @param  key the key
     * @throws IllegalArgumentException if key is null
     */
    public void delete(Key key) {
        if (key == null) throw new IllegalArgumentException("argument to delete() is null");

        int i = hash(key);
        for (int j = 0; j < table[i].length; j++) {
            if (table[i][j].occupied == true && table[i][j].key == key) {
                table[i][j].occupied = false;
                n--;
            }
        }

        // halves size of array if it's 12.5% full or less
        if (m > INIT_CAPACITY && n <= l * m / 8) resize(m/2);
    } 
}