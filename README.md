# IdentityHashMapFormalAnalysis
Deductive verification case study in which we formally verify [Java's `IdentityHashMap`] 
(http://hg.openjdk.java.net/jdk7u/jdk7u/jdk/file/4dd5e486620d/src/share/classes/java/util/IdentityHashMap.java).
We used the Java Modeling Language [JML](https://www.cs.ucf.edu/~leavens/JML/index.shtml) for formal specification 
and [KeY](https://www.key-project.org) as interactive theorem prover. 
We used [JJBMC](https://github.com/JonasKlamroth/JJBMC) and [JUnit](https://junit.org) to gain 
confidence while engineering the specification.

## The specified sources

The specified sources code can be found in the following 4 repositories:
* [IM9906-2-VerifyingIdentityHashMap](https://github.com/m4ndeb2r/IM9906-2-VerifyingIdentityHashMap) 
  contains the [JML](https://www.cs.ucf.edu/~leavens/JML/index.shtml) specification and the
  [KeY](https://www.key-project.org) proof files for every proven method. It also contains
  the binary of the KeY tool that was used to formally verify the `IdentityHashMap`.
* [IM9906-2-IdentityHashMapSpecTester](https://github.com/m4ndeb2r/IM9906-2-IdentityHashMapSpecTester) contains
  the [JUnit](https://junit.org) tests to gain confidence during the specification engineering process.
* [HashTableWithKeY](https://github.com/ChristianJ225/HashTableWithKeY) contains the sources of a 
  case study in which we looked at collision resolution strategies in relation to formal verification with KeY.
* [JJBMC](https://github.com/JonasKlamroth/JJBMC) contains the JJBMC codebase. JJBMC is a tool which enables 
  the software bounded model checker JBMC to verify contracts written in JML. 

# Publication

A report on the case study is currently under review.
