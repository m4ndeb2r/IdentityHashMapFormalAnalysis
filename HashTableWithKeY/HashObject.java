public final class HashObject {

	public final int value;

	public HashObject(int value) {
		this.value = value;
	}

	public final /*@ strictly_pure @*/ int getValue() {
		return value;
	}

	public final /*@ strictly_pure @*/ int hashCode() {
		return value;
	}

	public final /*@ strictly_pure @*/ boolean /*@ helper*/ equals(/*@ nullable @*/ Object otherObject) {
		if (!(otherObject instanceof HashObject)) return false;
		return this.value == ((HashObject) otherObject).getValue();
	}
}