package org.uacalc.util;

/**
 * Iterates an array of <code>int</code> indices
 * @author Jonah Horowitz
 */
public class SequenceIterator {
	private int min;
	private int max;
	private int[] current;
	private ArrayIncrementor inc;
	private boolean hasNext = true;

	public SequenceIterator(int[] start, int newMax, int newMin) {
		min=newMin;
		max=newMax;
		if ( start==null ) start = new int[0];
		current = new int[start.length];
		for ( int i = 0; i < start.length; i++ ) {
			current[i] = start[i];
		} // end for 0 <= i < start.length
		if ( current.length==0 ) hasNext=false;
		inc = SequenceGenerator.sequenceIncrementor(current, max, min);
	} // end constructor(int[], int, int)
	
	public int[] next() {
		int[] ans = new int[current.length];
		for ( int i = 0; i < current.length; i++ ) {
			ans[i]=current[i];
		}
		hasNext = inc.increment();
		return ans;
	} // end next()
	
	public boolean hasNext() {
		return hasNext;
	} // end hasNext()
} // end class SequenceIterator
