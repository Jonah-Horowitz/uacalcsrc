/* Malcev.java 2001/09/02  */

package org.uacalc.alg;

import java.util.*;
import org.uacalc.util.*;
import org.uacalc.terms.*;
import org.uacalc.alg.conlat.*;
import org.uacalc.alg.sublat.*;
//import org.apache.log4j.*;
import java.util.logging.*;

/**
 * A class with static methods for Mal'cev conditions such as finding
 * Jonsson terms, etc. It also has methods for related things such as
 * finding a near unamimity term of a given arity, finding a near 
 * majority term, etc.
 *
 * @version $Id$
 */
public class Malcev {

  static Logger logger = Logger.getLogger("org.uacalc.alg.Malcev");
  static {
    logger.setLevel(Level.FINER);
  }

  // make sure the class cannot be instantiated.
  private Malcev() {}

  /**
   * This will find a near unamimity term of the given arity
   * if one exits; otherwise it return <tt>null</tt>.
   */
  public static Term findNUF(SmallAlgebra alg, int arity) {
    if (alg.cardinality() == 1) return new VariableImp("x0");
    FreeAlgebra f2 = new FreeAlgebra(alg, 2);
    f2.makeOperationTables();
    final List gens = new ArrayList(arity);
    final Map termMap = new HashMap();
    for (int i = 0; i < arity ; i++) {
      final int[] arr = new int[arity];
      arr[i] = 1;
      IntArray ia = new IntArray(arr);
      gens.add(ia);
      termMap.put(ia, new VariableImp("x" + i));
    }
    BigProductAlgebra f2power = new BigProductAlgebra(f2, arity);
    final IntArray zero = new IntArray(new int[arity]);
    List sub = f2power.sgClose(gens, termMap, zero);
    if (sub.contains(zero)) return (Term)termMap.get(zero);
    return null;
  }

  /**
   * If \alpha = Cg(a,c) \meet Cg(a,b) 
   * and \beta = Cg(a,c) \meet Cg(b,c) this gives number of alteration
   * of \alpha and \beta to get from a to c in the join of \alpha and
   * \beta. It returns -1 if (a,c) is not in the join.
   */
  public static int localDistributivityLevel(int a, int b, int c, 
                                             SmallAlgebra alg) {
    final Partition cgab = alg.con().Cg(a,b);
    final Partition cgac = alg.con().Cg(a,c);
    final Partition cgbc = alg.con().Cg(b,c);
    return BasicPartition.permutabilityLevel(a, c, 
                                       cgac.meet(cgab), cgac.meet(cgbc));
  }

  /**
   * Find the max level  over all triples a, b, c, where,
   * if \alpha = Cg(a,c) \meet Cg(a,b) 
   * and \beta = Cg(a,c) \meet Cg(b,c) the level is the number of alteration
   * of \alpha and \beta to get from a to c in the join of \alpha and
   * \beta. It return -1 if for some triple, (a,c) is not in the join.
   */
  public static int localDistributivityLevel(SmallAlgebra alg) {
    final int size = alg.cardinality();
    int maxLevel = -1;
    for (int a = 0; a < size; a++) {
      for (int b = 0; b < size; b++) {
        for (int c = a + 1; c < size; c++) {  // a,c symmetry
          if (a == b || a == c || b == c) continue;
          BasicSet bs = alg.sub().sg(new int [] {a, b, c});
          Subalgebra sub = new Subalgebra(alg, bs);
          int level = localDistributivityLevel(sub.index(a), 
                                           sub.index(b), sub.index(c), sub);
          if (level == -1) return -1; // not distributive
          if (level > maxLevel) {
            maxLevel = level;
            logger.info("max level now is " + maxLevel);
          }
        }
      }
    }
    return maxLevel;
  }


  /**
   * Find a weak majority term for (the variety generated by) this 
   * algebra or <tt>null</tt> if there is none. 
   * A <i>weak majority term</i> is one satifying
   * <tt>m(x,x,x) = x</tt> and <tt>m(x,x,y) = m(x,y,x) = m(y,x,x)</tt>.
   * Any finite algebra that has relational width 3 (in the sense 
   * of the constraint satisfaction problem) must have a 
   * weak-majority term. Questions (that Matt told me about):
   * <br>
   * 1. is there a finite algebra with Jonsson terms but no weak 
   * majority term?
   * <br>
   * 2. is there a finite algebra with a weak unamimity term but no 
   * weak majority term?
   * <br>
   * The method looks in the subalgebra generated by (x,x,y,x),
   * (x,y,x,x), (y,x,x,x) for an element of the form (a,a,a,x).
   */
  public static Term weakMajorityTerm(SmallAlgebra alg) {
    return weakMajorityTerm(alg, false);
  }

  /**
   * Find a weak majority term for (the variety generated by) this 
   * algebra or <tt>null</tt> if there is none using a faster algorithm
   * if the algebra is idempotent. 
   */
  public static Term weakMajorityTerm(SmallAlgebra alg, boolean isIdempotent) {
    if (alg.cardinality() == 1)  return Variable.x;
    FreeAlgebra f2 = new FreeAlgebra(alg, 2);
    f2.makeOperationTables();
    logger.info("f2 size is " + f2.cardinality());
    IntArray g0;
    IntArray g1;
    IntArray g2;
    if (isIdempotent) {
      g0 = new IntArray(new int[] {0,0,1});
      g1 = new IntArray(new int[] {0,1,0});
      g2 = new IntArray(new int[] {1,0,0});
    }
    else {
      g0 = new IntArray(new int[] {0,0,1,0});
      g1 = new IntArray(new int[] {0,1,0,0});
      g2 = new IntArray(new int[] {1,0,0,0});
    }
    List gens = new ArrayList(3);
    gens.add(g0);
    gens.add(g1);
    gens.add(g2);
    final HashMap termMap = new HashMap(3);
    termMap.put(g0, Variable.x);
    termMap.put(g1, Variable.y);
    termMap.put(g2, Variable.z);
    //final IntArray yx = new IntArray(new int[] {1,0});
    BigProductAlgebra f2pow;
    if (isIdempotent) {
      f2pow = new BigProductAlgebra(f2, 3);
    }
    else {
      f2pow = new BigProductAlgebra(f2, 4);
    }
    // the yx argument means stop if yx is found. 
    // of course we want something different if we want the shortest term.
    List sub = f2pow.sgClose(gens, termMap);
    logger.info("sub alg of the " + (isIdempotent ? "third" : "fourth")
       + " power of f2 size " + sub.size());
    //if (sub.contains(yx)) return (Term)termMap.get(yx);
    IntArray ia = null;
    for (Iterator it = sub.iterator(); it.hasNext(); ) {
      ia = (IntArray)it.next();
      if (ia.get(0) == ia.get(1) && ia.get(1) == ia.get(2)) {
        if (isIdempotent) break;
        if (ia.get(3) == 0) break; // last coord is x
      }
      ia = null;
    }
    if (ia != null) return (Term)termMap.get(ia);
    return null;
  }

  /**
   * This returns a list of Jonsson terms witnessing distributivity, or 
   * null if the algebra does generate a congruence distributive variety.
   * It is guarenteed to be the least number of terms possible.
   */
  public static List jonssonTerms(SmallAlgebra alg) {
    List ans = new ArrayList();
    if (alg.cardinality() == 1) {
      ans.add(Variable.x);
      ans.add(Variable.z);
      return ans;
    }
    FreeAlgebra f2 = new FreeAlgebra(alg, 2);
    f2.makeOperationTables();
    logger.info("f2 size is " + f2.cardinality());
    IntArray g0 = new IntArray(new int[] {0,0,1});
    IntArray g1 = new IntArray(new int[] {0,1,0});
    IntArray g2 = new IntArray(new int[] {1,0,0});
    List gens = new ArrayList(3);
    gens.add(g0);
    gens.add(g1);
    gens.add(g2);
    final HashMap termMap = new HashMap(3);
    termMap.put(g0, Variable.x);
    termMap.put(g1, Variable.y);
    termMap.put(g2, Variable.z);
    BigProductAlgebra f2cubed = new BigProductAlgebra(f2, 3);
    final IntArray zero = new IntArray(new int[] {0,0,0});
    List sub = f2cubed.sgClose(gens, termMap, zero);
    logger.info("sub alg of f2 cubed size is " + sub.size());
    if (sub.contains(zero)) {
      logger.info("this variety has a ternary majority function");
      ans.add(Variable.x);
      ans.add(termMap.get(zero));
      ans.add(Variable.z);
      return ans;
    }
    List middleZero = new ArrayList();
    for (Iterator it = sub.iterator(); it.hasNext(); ) {
      IntArray ia = (IntArray)it.next();
      if (ia.get(1) == 0) middleZero.add(ia);
    }
    Comparator c = new Comparator() {
        public int compare(Object o1, Object o2) {
          IntArray ia1 = (IntArray)o1;
          IntArray ia2 = (IntArray)o2;
          for (int i = 0; i < ia1.size(); i++) {
            if (ia1.get(i) < ia2.get(i)) return -1;
            if (ia1.get(i) > ia2.get(i)) return 1;
          }
          return 0;
        }
        public boolean equals(Object o) { return false; }
    };
    Collections.sort(middleZero, c);
    for (Iterator it = middleZero.iterator(); it.hasNext(); ) {
      logger.finer("" + it.next());
    }
    final List path = jonssonLevelPath(middleZero, g0, g2);
    if (path == null) return null;
    for (Iterator it = path.iterator(); it.hasNext(); ) {
      IntArray ia = (IntArray)it.next();
      ans.add(termMap.get(ia));
    }
    return ans;
  }

  /**
   * This finds a path from g0 to g2 in <tt>middleZero</tt>, a list
   * of triples, where two triples are connected by an edge if either
   * their first or third coordinates agree.
   */
  public static List jonssonLevelPath(List middleZero, IntArray g0, 
                                                       IntArray g2) {
    // a list of lists of IntArray's
    final List levels = new ArrayList();
    final Map parentMap = new HashMap();
    List currentLevel = new ArrayList();
    //final HashSet visited = new HashSet();
    currentLevel.add(g0);
    parentMap.put(g0, null);
    levels.add(currentLevel);
    Comparator c0 = new Comparator() {
        public int compare(Object o1, Object o2) {
          return ((IntArray)o2).get(0) - ((IntArray)o1).get(0);
        }
    };
    Comparator c2 = new Comparator() {
        public int compare(Object o1, Object o2) {
          return ((IntArray)o2).get(2) - ((IntArray)o1).get(2);
        }
    };
    HashMap classes0 = new HashMap();
    HashMap classes2 = new HashMap();
    for (Iterator it = middleZero.iterator(); it.hasNext(); ) {
      IntArray ia = (IntArray)it.next();
      Integer ia_0 = new Integer(ia.get(0));
      Integer ia_2 = new Integer(ia.get(2));
      List eqclass = (List)classes0.get(ia_0);
      if (eqclass == null) {
        eqclass = new ArrayList();
        classes0.put(ia_0, eqclass);
      }
      eqclass.add(ia);
      eqclass = (List)classes2.get(ia_2);
      if (eqclass == null) {
        eqclass = new ArrayList();
        classes2.put(ia_2, eqclass);
      }
      eqclass.add(ia);
    } 
    boolean even = false;
    while (true) {
      even = !even;
      final List nextLevel = new ArrayList();
//System.out.println("current level size = " + currentLevel.size());
      for (Iterator it = currentLevel.iterator(); it.hasNext(); ) {
        IntArray ia = (IntArray)it.next();
        List eqclass;
        if (even) eqclass = (List)classes0.get(new Integer(ia.get(0)));
        else eqclass = (List)classes2.get(new Integer(ia.get(2)));
        //eqclass.remove(ia);
        for (Iterator it2 = eqclass.iterator(); it2.hasNext(); ) {
          IntArray ia2 = (IntArray)it2.next();
          //if (ia2.equals(ia)) continue;
          if (!parentMap.containsKey(ia2)) {
            parentMap.put(ia2, ia);
            nextLevel.add(ia2);
          }
          if (ia2.equals(g2)) {
            final List path = new ArrayList(levels.size() + 1);
            path.add(g2);
            ia2 = (IntArray)parentMap.get(ia2);
            while (ia2 != null) {
              path.add(ia2);
              ia2 = (IntArray)parentMap.get(ia2);
            }
            Collections.reverse(path);
            logger.fine("path");
            for (Iterator iter = path.iterator(); iter.hasNext(); ) {
              logger.fine("" + iter.next());
            }
            return path;
          }
        }
      }
      if (nextLevel.isEmpty()) break;    
      levels.add(nextLevel);
      currentLevel = nextLevel;
    }
    return null;
  }

  /**
   * If this algebra generates a distributive variety, this returns
   * the minimal number of Jonsson terms minus 1; otherwise it returns -1,
   * but it is probably better to use <tt>jonssonTerms</tt> and get
   * get the actual terms.
   * So congruence distributivity can be tested by seeing if this 
   * this is positive. If the algebra has only one element, it returns 1.
   * For a lattice it returns 2. For Miklos Marioti's 5-ary near unanimity
   * operation on a 4 element set, it returns 6 (the maximum possible).
   */
  public static int jonssonLevel(SmallAlgebra alg) {
    if (alg.cardinality() == 1) return 1;
    FreeAlgebra f2 = new FreeAlgebra(alg, 2);
    f2.makeOperationTables();
    logger.info("f2 size is " + f2.cardinality());
    IntArray g0 = new IntArray(new int[] {0,0,1});
    IntArray g1 = new IntArray(new int[] {0,1,0});
    IntArray g2 = new IntArray(new int[] {1,0,0});
    List gens = new ArrayList(3);
    gens.add(g0);
    gens.add(g1);
    gens.add(g2);
    final HashMap termMap = new HashMap(3);
    termMap.put(g0, Variable.x);
    termMap.put(g1, Variable.y);
    termMap.put(g2, Variable.z);
    BigProductAlgebra f2cubed = new BigProductAlgebra(f2, 3);
    List sub = f2cubed.sgClose(gens, termMap);
    logger.info("sub alg of f2 cubed size is " + sub.size());
    final IntArray zero = new IntArray(new int[] {0,0,0});
    if (sub.contains(zero)) {
      logger.info("this variety has a ternary majority function");
      return 2;
    }
    List middleZero = new ArrayList();
    for (Iterator it = sub.iterator(); it.hasNext(); ) {
      IntArray ia = (IntArray)it.next();
      if (ia.get(1) == 0) middleZero.add(ia);
    }
    Comparator c = new Comparator() {
        public int compare(Object o1, Object o2) {
          IntArray ia1 = (IntArray)o1;
          IntArray ia2 = (IntArray)o2;
          for (int i = 0; i < ia1.size(); i++) {
            if (ia1.get(i) < ia2.get(i)) return -1;
            if (ia1.get(i) > ia2.get(i)) return 1;
          }
          return 0;
        }
        public boolean equals(Object o) { return false; }
    };
    Collections.sort(middleZero, c);
    return jonssonLevelAux(middleZero, g0, g2);
  }

  public static int jonssonLevelAux(List middleZero, IntArray g0,
                                              IntArray g2) {
    // a list of lists of IntArray's
    final List levels = new ArrayList();
    List currentLevel = new ArrayList();
    final HashSet visited = new HashSet();
    currentLevel.add(new IntArray[] {g0, null});
    visited.add(g0);
    levels.add(currentLevel);
    Comparator c0 = new Comparator() {
        public int compare(Object o1, Object o2) {
          return ((IntArray)o2).get(0) - ((IntArray)o1).get(0);
        }
    };
    Comparator c2 = new Comparator() {
        public int compare(Object o1, Object o2) {
          return ((IntArray)o2).get(2) - ((IntArray)o1).get(2);
        }
    };
    HashMap classes0 = new HashMap();
    HashMap classes2 = new HashMap();
    for (Iterator it = middleZero.iterator(); it.hasNext(); ) {
      IntArray ia = (IntArray)it.next();
      Integer ia_0 = new Integer(ia.get(0));
      Integer ia_2 = new Integer(ia.get(2));
      List eqclass = (List)classes0.get(ia_0);
      if (eqclass == null) {
        eqclass = new ArrayList();
        classes0.put(ia_0, eqclass);
      }
      eqclass.add(ia);
      eqclass = (List)classes2.get(ia_2);
      if (eqclass == null) {
        eqclass = new ArrayList();
        classes2.put(ia_2, eqclass);
      }
      eqclass.add(ia);
    } 
    boolean even = false;
    while (true) {
      if (even) even = false;
      else even = true;
      final List nextLevel = new ArrayList();
//System.out.println("current level size = " + currentLevel.size());
      for (Iterator it = currentLevel.iterator(); it.hasNext(); ) {
        IntArray ia = ((IntArray[])it.next())[0];
        List eqclass;
        if (even) eqclass = (List)classes0.get(new Integer(ia.get(0)));
        else eqclass = (List)classes2.get(new Integer(ia.get(2)));
        //eqclass.remove(ia);
        for (Iterator it2 = eqclass.iterator(); it2.hasNext(); ) {
          IntArray ia2 = (IntArray)it2.next();
          //if (ia2.equals(ia)) continue;
          if (ia2.equals(g2)) {
//System.out.println("returning " + (levels.size() + 1));

            return levels.size();
          }
          if (!visited.contains(ia2)) {
            visited.add(ia2);
            nextLevel.add(new IntArray[] {ia2, ia});
          }
        }
      }
      if (nextLevel.isEmpty()) break;    
      levels.add(nextLevel);
      currentLevel = nextLevel;
//System.out.println("levels size is " + levels.size());
    }
    return -1;
  }

  /**
   * Find a Day quadruple of the form a = (x0, x1), b = (x0, y1),
   * c = y0, x1), d = (y0, y1). Since Day quadruples are invariant
   * undere the permutation (ab)(cd), we can take x1 &lt; y1.
   *
   */
  public static IntArray findDayQuadrupleInSquare(final SmallAlgebra alg) {
    final int n = alg.cardinality();
    final BigProductAlgebra sq = new BigProductAlgebra(alg, 2);
    final IntArray a = new IntArray(2);
    final IntArray b = new IntArray(2);
    final IntArray c = new IntArray(2);
    final IntArray d = new IntArray(2);
    final int[] avec = a.toArray();
    final int[] bvec = b.toArray();
    final int[] cvec = c.toArray();
    final int[] dvec = d.toArray();
    final List gens = new ArrayList(4);
    gens.add(a);
    gens.add(b);
    gens.add(c);
    gens.add(d);
    for (int x0 = 0; x0 < n; x0++) {
      for (int x1 = 0; x1 < n; x1++) {
        for (int y0 = 0; y0 < n; y0++) {
          for (int y1 = x1 + 1; y1 < n; y1++) {
            avec[0] = x0;
            avec[1] = x1;
            bvec[0] = x0;
            bvec[1] = y1;
            cvec[0] = y0;
            cvec[1] = x1;
            dvec[0] = y0;
            dvec[1] = y1;
            final SmallAlgebra sub = new SubProductAlgebra("", sq, gens);
            if (dayQuadruple(sub.elementIndex(a), sub.elementIndex(b),
                             sub.elementIndex(c), sub.elementIndex(d), sub)) {
              return new IntArray(new int[] {x0, x1, y0, y1});
            }
          }
        }
      }
    }
    return null;
  }


  public static boolean dayQuadruple(int a, int b, int c, int d,
                                                     SmallAlgebra alg) {
    final Partition cgcd = alg.con().Cg(c,d);
    final Partition cgab_cd = alg.con().Cg(a,b).join(cgcd);
    final Partition cgac_bd = alg.con().Cg(a,c).join(alg.con().Cg(b, d));
    return !cgcd.join(cgab_cd.meet(cgac_bd)).isRelated(a,b);
  }

  public static boolean congruenceModularVariety(SmallAlgebra alg) {
    FreeAlgebra f2 = new FreeAlgebra(alg, 2);
    f2.makeOperationTables();
    //List gens = f2.generators();
    IntArray a = new IntArray(new int[] {0,0});
    IntArray b = new IntArray(new int[] {0,1});
    IntArray c = new IntArray(new int[] {1,0});
    IntArray d = new IntArray(new int[] {1,1});
    List gens = new ArrayList(4);
    gens.add(a);
    gens.add(b);
    gens.add(c);
    gens.add(d);
    BigProductAlgebra f2squared = new BigProductAlgebra(f2, 2);
    //List sub = f2squared.sgClose(gens, termMap);
    SmallAlgebra sub = new SubProductAlgebra("", f2squared, gens);
    sub.makeOperationTables();
    logger.info("sub alg of f2 square size is " + sub.cardinality());
    Partition cgcd = sub.con().Cg(c, d);
    return cgcd.isRelated(sub.elementIndex(a), sub.elementIndex(b));
  }


  /**
   * This returns a list of Gumm terms witnessing modularity, or null if 
   * the algebra does generate a congruence modular variety.
   * It is guarenteed to be the least number of terms possible.
   */
  public static List gummTerms(SmallAlgebra alg) {
    List ans = new ArrayList();
    if (alg.cardinality() == 1) {
      ans.add(Variable.x);
      ans.add(Variable.z);
      return ans;
    }
    FreeAlgebra f2 = new FreeAlgebra(alg, 2);
    f2.makeOperationTables();
    logger.info("f2 size is " + f2.cardinality());
    IntArray g0 = new IntArray(new int[] {0,0,1});
    IntArray g1 = new IntArray(new int[] {0,1,0});
    IntArray g2 = new IntArray(new int[] {1,0,0});
    List gens = new ArrayList(3);
    gens.add(g0);
    gens.add(g1);
    gens.add(g2);
    final HashMap termMap = new HashMap(3);
    termMap.put(g0, Variable.x);
    termMap.put(g1, Variable.y);
    termMap.put(g2, Variable.z);
    BigProductAlgebra f2cubed = new BigProductAlgebra(f2, 3);
    List sub = f2cubed.sgClose(gens, termMap);
    logger.info("sub alg of f2 cubed size is " + sub.size());
    final IntArray zero = new IntArray(new int[] {0,0,0});
    if (sub.contains(zero)) {
      logger.info("this variety has a ternary majority function");
      ans.add(Variable.x);
      ans.add(termMap.get(zero));
      ans.add(Variable.z);
      return ans;
    }
    List middleZero = new ArrayList();
    for (Iterator it = sub.iterator(); it.hasNext(); ) {
      IntArray ia = (IntArray)it.next();
      if (ia.get(1) == 0) middleZero.add(ia);
    }
    List firstOne = new ArrayList();
    for (Iterator it = sub.iterator(); it.hasNext(); ) {
      IntArray ia = (IntArray)it.next();
      if (ia.get(0) == 1) firstOne.add(ia);
    }
    final Comparator c = new Comparator() {
        public int compare(Object o1, Object o2) {
          IntArray ia1 = (IntArray)o1;
          IntArray ia2 = (IntArray)o2;
          for (int i = 0; i < ia1.size(); i++) {
            if (ia1.get(i) < ia2.get(i)) return -1;
            if (ia1.get(i) > ia2.get(i)) return 1;
          }
          return 0;
        }
        public boolean equals(Object o) { return false; }
    };
    Collections.sort(middleZero, c);
    //Collections.sort(firstOne, c);
    for (Iterator it = middleZero.iterator(); it.hasNext(); ) {
      logger.finer("" + it.next());
    }
    final List path = gummLevelPath(middleZero, firstOne, g0, g2);
    if (path == null) return null;
    for (Iterator it = path.iterator(); it.hasNext(); ) {
      IntArray ia = (IntArray)it.next();
      ans.add(termMap.get(ia));
    }
    return ans;
  }

  /**
   * Change this a little:
   * This finds a path from g0 to u, then v. The path from g0 to u is 
   * in <tt>middleZero</tt>, and u and v agree on the third coordinate
   * and v has 1 (the second free generator of F_2) in its first 
   * coordinate. The path from g0 to u is a a list
   * of triples, where two triples are connected by an edge if either
   * their first or third coordinates agree.
   */
  public static List gummLevelPath(List middleZero, List firstOne, 
                                             IntArray g0, IntArray g2) {
    // a list of lists of IntArray's
    final List levels = new ArrayList();
    final Map parentMap = new HashMap();
    List currentLevel = new ArrayList();
    //final HashSet visited = new HashSet();
    currentLevel.add(g0);
    parentMap.put(g0, null);
    levels.add(currentLevel);
    Comparator c0 = new Comparator() {
        public int compare(Object o1, Object o2) {
          return ((IntArray)o2).get(0) - ((IntArray)o1).get(0);
        }
    };
    Comparator c2 = new Comparator() {
        public int compare(Object o1, Object o2) {
          return ((IntArray)o2).get(2) - ((IntArray)o1).get(2);
        }
    };
    HashMap classes0 = new HashMap();
    HashMap classes2 = new HashMap();
    for (Iterator it = middleZero.iterator(); it.hasNext(); ) {
      IntArray ia = (IntArray)it.next();
      Integer ia_0 = new Integer(ia.get(0));
      Integer ia_2 = new Integer(ia.get(2));
      List eqclass = (List)classes0.get(ia_0);
      if (eqclass == null) {
        eqclass = new ArrayList();
        classes0.put(ia_0, eqclass);
      }
      eqclass.add(ia);
      eqclass = (List)classes2.get(ia_2);
      if (eqclass == null) {
        eqclass = new ArrayList();
        classes2.put(ia_2, eqclass);
      }
      eqclass.add(ia);
    }
    // classes1 is for the firstOne
    HashMap classes1 = new HashMap();
    for (Iterator it = firstOne.iterator(); it.hasNext(); ) {
      IntArray ia = (IntArray)it.next();
      Integer ia_2 = new Integer(ia.get(2));
      List eqclass = (List)classes1.get(ia_2);
      if (eqclass == null) {
        eqclass = new ArrayList();
        classes1.put(ia_2, eqclass);
      }
      eqclass.add(ia);
    }
    boolean even = false;
    while (true) {
      even = !even;
      final List nextLevel = new ArrayList();
//System.out.println("current level size = " + currentLevel.size());
      for (Iterator it = currentLevel.iterator(); it.hasNext(); ) {
        IntArray ia = (IntArray)it.next();
        List eqclass;
        if (even) eqclass = (List)classes0.get(new Integer(ia.get(0)));
        else eqclass = (List)classes2.get(new Integer(ia.get(2)));
        //eqclass.remove(ia);
        for (Iterator it2 = eqclass.iterator(); it2.hasNext(); ) {
          IntArray ia2 = (IntArray)it2.next();
          //if (ia2.equals(ia)) continue;
          if (!parentMap.containsKey(ia2)) {
            parentMap.put(ia2, ia);
            nextLevel.add(ia2);
          }
          // here
          eqclass = (List)classes1.get(new Integer(ia2.get(2)));
          if (eqclass != null) {
            IntArray p = (IntArray)eqclass.get(0);
            if (eqclass.contains(g2)) p = g2;
            final List path = new ArrayList(levels.size() + 1);
            if (!eqclass.contains(ia2)) path.add(p);
            path.add(ia2);
            ia2 = (IntArray)parentMap.get(ia2);
            while (ia2 != null) {
              path.add(ia2);
              ia2 = (IntArray)parentMap.get(ia2);
            }
            Collections.reverse(path);
            logger.fine("path");
            for (Iterator iter = path.iterator(); iter.hasNext(); ) {
              logger.fine("" + iter.next());
            }
            return path;
          }
        }
      }
      if (nextLevel.isEmpty()) break;    
      levels.add(nextLevel);
      currentLevel = nextLevel;
    }
    return null;
  }

  /**
   * Find a Mal'cev term for (the variety generated by) this algebra or
   * null if there is it is not permutable.
   */
  public static Term malcevTerm(SmallAlgebra alg) {
    if (alg.cardinality() == 1)  return Variable.x;
    FreeAlgebra f2 = new FreeAlgebra(alg, 2);
    f2.makeOperationTables();
    logger.info("f2 size is " + f2.cardinality());
    IntArray g0 = new IntArray(new int[] {0,0});
    IntArray g1 = new IntArray(new int[] {0,1});
    IntArray g2 = new IntArray(new int[] {1,1});
    List gens = new ArrayList(3);
    gens.add(g0);
    gens.add(g1);
    gens.add(g2);
    final HashMap termMap = new HashMap(3);
    termMap.put(g0, Variable.x);
    termMap.put(g1, Variable.y);
    termMap.put(g2, Variable.z);
    final IntArray yx = new IntArray(new int[] {1,0});
    BigProductAlgebra f2squared = new BigProductAlgebra(f2, 2);
    // the yx argument means stop if yx is found. 
    // of course we want something different if we want the shortest term.
    List sub = f2squared.sgClose(gens, termMap, yx);
    logger.info("sub alg of f2 squared size is " + sub.size());
    if (sub.contains(yx)) return (Term)termMap.get(yx);
    return null;
  }

  /**
   * Find a Pixley term for (the variety generated by) this algebra or
   * null if there is it is not arithmetic.
   * The algorithm looks at the subalgebra of F(x,y)^3 generated by
   * (x,x,y), (y,y,y), (y,x,x) and looks for (x,x,x).
   */
  public static Term pixleyTerm(SmallAlgebra alg) {
    if (alg.cardinality() == 1)  return Variable.x;
    FreeAlgebra f2 = new FreeAlgebra(alg, 2);
    f2.makeOperationTables();
    logger.info("f2 size is " + f2.cardinality());
    IntArray g0 = new IntArray(new int[] {0,0,1});
    IntArray g1 = new IntArray(new int[] {1,1,1});
    IntArray g2 = new IntArray(new int[] {1,0,0});
    List gens = new ArrayList(3);
    gens.add(g0);
    gens.add(g1);
    gens.add(g2);
    final HashMap termMap = new HashMap();
    termMap.put(g0, Variable.x);
    termMap.put(g1, Variable.y);
    termMap.put(g2, Variable.z);
    final IntArray xxx = new IntArray(new int[] {0,0,0});
    BigProductAlgebra f2cubed = new BigProductAlgebra(f2, 3);
    // the yx argument means stop if yx is found. 
    // of course we want something different if we want the shortest term.
    List sub = f2cubed.sgClose(gens, termMap, xxx);
    logger.info("sub alg of f2 cubed size is " + sub.size());
    if (sub.contains(xxx)) return (Term)termMap.get(xxx);
    return null;
  }

  /**
   * This returns a list of Hagemann Mitschke Terms terms witnessing 
   * <code>k</code>-permutability, or
   * null if the algebra does generate a congruence 
   * <code>k</code>-permutable variety.
   * It is guarenteed to be the least number of terms possible.
   */
  public static List hagemannMitschkeTerms(SmallAlgebra alg) {
    List ans = new ArrayList();
    if (alg.cardinality() == 1) {
      ans.add(Variable.x);
      ans.add(Variable.z);
      return ans;
    }
    FreeAlgebra f2 = new FreeAlgebra(alg, 2);
    f2.makeOperationTables();
    logger.info("f2 size is " + f2.cardinality());
    IntArray g0 = new IntArray(new int[] {0,0});
    IntArray g1 = new IntArray(new int[] {0,1});
    IntArray g2 = new IntArray(new int[] {1,1});
    List gens = new ArrayList(3);
    gens.add(g0);
    gens.add(g1);
    gens.add(g2);
    final HashMap termMap = new HashMap(3);
    termMap.put(g0, Variable.x);
    termMap.put(g1, Variable.y);
    termMap.put(g2, Variable.z);
    final IntArray yx = new IntArray(new int[] {1,0});
    BigProductAlgebra f2squared = new BigProductAlgebra(f2, 2);
    // the yx argument means stop if yx is found. 
    // of course we want something different if we want the shortest term.
    List sub = f2squared.sgClose(gens, termMap, yx);
    logger.info("sub alg of f2 squared size is " + sub.size());
    if (sub.contains(yx)) {
      logger.info("this variety has a Malcev term");
      ans.add(Variable.x);
      ans.add(termMap.get(yx));
      ans.add(Variable.z);
      return ans;
    }
    // Not sure we need this. Check if we need to sort this.
    Comparator c = new Comparator() {
        public int compare(Object o1, Object o2) {
          IntArray ia1 = (IntArray)o1;
          IntArray ia2 = (IntArray)o2;
          for (int i = 0; i < ia1.size(); i++) {
            if (ia1.get(i) < ia2.get(i)) return -1;
            if (ia1.get(i) > ia2.get(i)) return 1;
          }
          return 0;
        }
        public boolean equals(Object o) { return false; }
    };
    Collections.sort(sub, c);
    final List path = hagemannMitschkeLevelPath(sub, g0, g2);
    if (path == null) return null;
    for (Iterator it = path.iterator(); it.hasNext(); ) {
      IntArray ia = (IntArray)it.next();
      ans.add(termMap.get(ia));
    }
    return ans;
  }

  /**
   * This finds a path from g0 to g2 in <tt>middleZero</tt>, a list
   * of triples, where two triples are connected by an edge if either
   * their first or third coordinates agree.
   */
  public static List hagemannMitschkeLevelPath(List sub, IntArray g0, 
                                                         IntArray g2) {
    // a list of lists of IntArray's
    final List levels = new ArrayList();
    final Map parentMap = new HashMap();
    List currentLevel = new ArrayList();
    //final HashSet visited = new HashSet();
    currentLevel.add(g0);
    parentMap.put(g0, null);
    levels.add(currentLevel);
    Comparator c0 = new Comparator() {
        public int compare(Object o1, Object o2) {
          return ((IntArray)o2).get(0) - ((IntArray)o1).get(0);
        }
    };
    Comparator c2 = new Comparator() {
        public int compare(Object o1, Object o2) {
          return ((IntArray)o2).get(1) - ((IntArray)o1).get(1);
        }
    };
    HashMap classes0 = new HashMap();
    HashMap classes1 = new HashMap();
    for (Iterator it = sub.iterator(); it.hasNext(); ) {
      IntArray ia = (IntArray)it.next();
      Integer ia_0 = new Integer(ia.get(0));
      Integer ia_1 = new Integer(ia.get(1));
      List eqclass = (List)classes0.get(ia_0);
      if (eqclass == null) {
        eqclass = new ArrayList();
        classes0.put(ia_0, eqclass);
      }
      eqclass.add(ia);
      eqclass = (List)classes1.get(ia_1);
      if (eqclass == null) {
        eqclass = new ArrayList();
        classes1.put(ia_1, eqclass);
      }
      eqclass.add(ia);
    } 
    while (true) {
      final List nextLevel = new ArrayList();
//System.out.println("current level size = " + currentLevel.size());
      for (Iterator it = currentLevel.iterator(); it.hasNext(); ) {
        IntArray ia = (IntArray)it.next();
        List eqclass;
        eqclass = (List)classes1.get(new Integer(ia.get(0)));
        for (Iterator it2 = eqclass.iterator(); it2.hasNext(); ) {
          IntArray ia2 = (IntArray)it2.next();
          if (!parentMap.containsKey(ia2)) {
            parentMap.put(ia2, ia);
            nextLevel.add(ia2);
          }
          if (ia2.equals(g2)) {
            final List path = new ArrayList(levels.size() + 1);
            path.add(g2);
            ia2 = (IntArray)parentMap.get(ia2);
            while (ia2 != null) {
              path.add(ia2);
              ia2 = (IntArray)parentMap.get(ia2);
            }
            Collections.reverse(path);
            logger.fine("Hagemann Mitschke path");
            for (Iterator iter = path.iterator(); iter.hasNext(); ) {
              logger.fine("" + iter.next());
            }
            return path;
          }
        }
      }
      if (nextLevel.isEmpty()) break;    
      levels.add(nextLevel);
      currentLevel = nextLevel;
    }
    return null;
  }


  public static void main(String[] args) {
    if (args.length == 0) return;
    SmallAlgebra alg0 = null;
    int arity = 3;
    try {
      alg0 = (SmallAlgebra)org.uacalc.io.AlgebraIO.readAlgebraFile(args[0]);
      if (args.length > 1) {
        arity = Integer.parseInt(args[1]);
      }
    }
    catch (Exception e) {}
    //int level = Malcev.jonssonLevel(alg0);
    //System.out.println("level is " + level);

    //Term t = findNUF(alg0, arity);
    //if (t == null) System.out.println("there is no NUF with arity " + arity);
    //else System.out.println("the alg has a NUF of arity " + arity + ": " + t);

    IntArray ia = findDayQuadrupleInSquare(alg0);
    System.out.println("day quad is " + ia);
  }



}







