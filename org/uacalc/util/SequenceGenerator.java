/* SequenceGenerator.java (c) 2004/11/11  Ralph Freese */

package org.uacalc.util;

import java.util.*;

/**
 * This has utility static methods for sequence generation,
 * including nondecreasing sequences. It also
 * includes an in-place ArrayIncrementor.
 */
public final class SequenceGenerator {

  protected SequenceGenerator() {}

  /**
   * This increments an array in place through all nondecreasing sequences
   * whose entries lie between 0 and <tt>max</tt>, inclusive.
   */
  public static ArrayIncrementor nondecreasingSequenceIncrementor(
                                          final int[] a, final int max) {
    return nondecreasingSequenceIncrementor(a, max, 0);
  }

  /**
   * This increments an array in place through all nondecreasing sequences
   * whose entries lie between 0 and <tt>max</tt>, inclusive,
   * subject to the restrction that last coordiate is at 
   * least <tt>lastMin</tt> (useful when the first part of a list is 
   * known to be closed). 
   */
  public static ArrayIncrementor nondecreasingSequenceIncrementor(
                           final int[] a, final int max, final int lastMin) {
    return new ArrayIncrementor() {
        public boolean increment() {
          if (a[0] >= max) return false;
          incrementNondecreasingSequence(a, max, lastMin);
          return true;
        }
      };
  }

  /**
   * Generate the next nondecreasing sequence 
   * on <tt>0</tt> to <tt>max - 1</tt> subject to the restriction that
   * last coordinate is at least <tt>lastMin</tt>.
   */
  private static void incrementNondecreasingSequence(int[] arg, 
                                                    int max, int lastMin) {
    final int len = arg.length;
    for (int i = len - 1; i >= 0; i--) {
      if (arg[i] < max) {
        final int k = arg[i] + 1;
        for (int j = i; j < len; j++) {
          arg[j] = k;
        }
        if (arg[len - 1] < lastMin) arg[len - 1] = lastMin;
        break;
      }
    }
  }

  /**
   * his increments an array in place through all strictly increasing sequences
   * whose entries lie between 0 and <tt>max</tt>, inclusive.
   * 
   * @param a
   * @param max
   * @return
   */
  public static ArrayIncrementor increasingSequenceIncrementor(final int[] a, final int max) {
    final int len = a.length;
    final int[] a2 = new int[len];
    final ArrayIncrementor nondecInc = nondecreasingSequenceIncrementor(a2, max + 1 - len);
    return new ArrayIncrementor() {
        public boolean increment() {
          boolean v = nondecInc.increment();
          if (!v) return false;
          for (int i = 0; i <  len; i++) {
            a[i] = a2[i] + i;
          }
          return true;
        }
    };
  }
  
  /**
   * This just increments the array through all possible tuples
   * with entries between 0 and max. This increments from the right:
   * [0,0,0], [0,0,1], ...,[max,max,max].
   */
  public static ArrayIncrementor sequenceIncrementor(
                                            final int[] a, final int max) {
    return new ArrayIncrementor() {
        public boolean increment() {
          final int len = a.length;
          for (int i = len - 1; i >= 0; i--) {
            if (a[i] < max) {
              a[i]++;
              for (int j = i + 1; j < len; j++) {
                a[j] = 0;
              }
              return true;
            }
          }
          return false;
        }
      };
  }

  /**
   * This just increments the array through all possible tuples
   * with entries between 0 and <code>max</code> and having at 
   * least one entry at least as large as <code>min</code>.
   * This increments from the right: * [0,0,0], [0,0,1], ...,[max,max,max]. 
   * Of course <code>min</code> should be at most <code>max</code>.
   */
  public static ArrayIncrementor sequenceIncrementor(
                          final int[] a, final int max, final int min) {
    return new ArrayIncrementor() {
        public boolean increment() {
          final int len = a.length;
          for (int i = len - 1; i >= 0; i--) {
            if (a[i] < max) {
              a[i]++;
              for (int j = i + 1; j < len; j++) {
                a[j] = 0;
              }
              boolean ok = false;
              for (int j = i; j >= 0; j--) {
                if (a[j] >= min) {
                  ok = true;
                  break;
                }
              }
              if (!ok) a[len - 1] = min;
              return true;
            }
          }
          return false;
        }
      };
  }
  
  /**
   * This just increments the array through all possible tuples
   * with entries between 0 and <code>max</code> and having at 
   * least one entry at least as large as <code>min</code>.
   * This increments from the right: * [0,0,0], [0,0,1], ...,[max,max,max]. 
   * Of course <code>min</code> should be at most <code>max</code>.
   * 
   * <code>jump</code> indicates how many times the array will be 
   * incremented by each call to increment(). This is used in 
   * parallel processing.
   * 
   */
  public static ArrayIncrementor sequenceIncrementor(
                          final int[] a, final int max, final int min, final int jump) {
    return new ArrayIncrementor() {
        public boolean increment() {
          for (int k = 0; k < jump; k++) {
            if (!incrementAux()) return false;
          }
          return true;
        }
        private boolean incrementAux() {
          final int len = a.length;
          for (int i = len - 1; i >= 0; i--) {
            if (a[i] < max) {
              a[i]++;
              for (int j = i + 1; j < len; j++) {
                a[j] = 0;
              }
              boolean ok = false;
              for (int j = i; j >= 0; j--) {
                if (a[j] >= min) {
                  ok = true;
                  break;
                }
              }
              if (!ok) a[len - 1] = min;
              return true;
            }
          }
          return false;
        }
      };
  }

  public static ArrayIncrementor blockSequenceIncrementor( final int[] a, final int max, final int min, final int jump ) {
	  return new ArrayIncrementor() {
		  public boolean increment() {
			  boolean ans=incrementAux();
			  while (!anyOver()) ans=incrementAux();
			  return ans;
		  } // end increment()
		  
		  public boolean anyOver() {
			  for ( int i = 0; i < a.length; i++ ) if ( a[i]>=min ) return true;
			  return false;
		  } // end anyOver()
		  
		  public boolean incrementAux() {
			  a[a.length-1]+=jump;
			  for ( int i = a.length-1; i>0; i-- ) while (a[i]>max) {
				  a[i]-=max;
				  a[i-1]++;
			  } // end while (a[i]>max)
			  return a[0]<=max;
		  } // end incrementAux()
	  };
  } // end blockSequenceIncrementor(int[], int, int, int)
  
  /**
   * This just increments the array through all possible tuples
   * with entries between 0 and max from the left. This increments 
   * from the left: [0,0,0], [1,0,0], ..., [max,max,max].
   */
  public static ArrayIncrementor leftSequenceIncrementor(
                                            final int[] a, final int max) {
    return new ArrayIncrementor() {
        public boolean increment() {
          boolean ans = false;
          final int len = a.length;
          for (int i = 0; i < len; i++) {
            if (a[i] < max) {
              a[i]++;
              for (int j = i - 1; j >= 0; j--) {
                a[j] = 0;
              }
              return true;
            }
          }
          return false;
        }
      };
  }

  /**
   * Generate the next sequence 
   * on <tt>0</tt> to <tt>max - 1</tt>.
   */
  private static void incrementSequence(int[] arg, final int max) {
    final int len = arg.length;
    for (int i = len - 1; i >= 0; i--) {
      if (arg[i] < max) {
        arg[i]++;
        break;
      }
    }
  }

  public static void main(String[] args) {
    //int[] a = new int[] {0,0,0,0,0};
    //ArrayIncrementor inc = nondecreasingSequenceIncrementor(a, 3, 2);
    //ArrayIncrementor inc = nondecreasingSequenceIncrementor(a, 3, 2);
    //int[] a = new int[] {0,0,0};
    //ArrayIncrementor inc = sequenceIncrementor(a, 3, 2);
    //while (inc.increment()) {
    //  System.out.println(ArrayString.toString(a));
    //}
    //int[] a = new int[] {0,1,2};
    //ArrayIncrementor inc = increasingSequenceIncrementor(a, 4);
    int[] a = new int[] {0, 4};
    int[] a2 = new int[] {0, 5};
    ArrayIncrementor inc = sequenceIncrementor(a, 5, 4, 2);
    ArrayIncrementor inc2 = sequenceIncrementor(a2, 5, 4, 2);
    System.out.println(ArrayString.toString(a) + "  " + ArrayString.toString(a2));
    while (true) {
      if (!inc.increment()) break;
      System.out.print(ArrayString.toString(a));
      System.out.print("  ");
      if (!inc2.increment()) break;
      System.out.println(ArrayString.toString(a2));
    }
    System.out.println("");
  }


}
