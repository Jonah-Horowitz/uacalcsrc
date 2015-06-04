package org.uacalc.util;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.function.BiFunction;
import java.io.FileNotFoundException;
import java.io.PrintStream;

/**
 * Utility for generating index tuples for elements of algebras.
 * @author Jonah Horowitz
 *
 */
public class Indexer {
	public static final HashMap<int[],GeneralIndexFunction> generalIndexFunctions = new HashMap<int[],GeneralIndexFunction>();
	public static final HashMap<int[],HornerFunction> hornerIndexFunctions = new HashMap<int[],HornerFunction>();
	
	/**
	 * Clears all stored index functions, use only in order to save RAM.
	 */
	public static void purgeIndexFunctions() {
		generalIndexFunctions.clear();
		hornerIndexFunctions.clear();
	}
	
	/**
	 * A general index function.
	 * @author jhorowitz
	 *
	 */
	public static class GeneralIndexFunction implements BiFunction<Long,int[],int[]> {
		private final int kval;
		private final int nval;
		private final int mval;
		private final BigInteger nk;
		private final BigInteger base;
		private final BigInteger mbase;
		
		/**
		 * Creates a new general index function.
		 * @param n  The size of the universe.
		 * @param m  The indices to ignore.
		 * @param k  The length of the tuples.
		 */
		public GeneralIndexFunction(int n, int m, int k) {
			kval=k;
			nval=n;
			mval=m;
			nk=BigInteger.valueOf(n).pow(k-1);
			base=nk.subtract(BigInteger.valueOf(m).pow(k-1));
			mbase=base.multiply(BigInteger.valueOf(m));
		}

		@Override
		public int[] apply(Long t, int[] u) {
			BigInteger i = BigInteger.valueOf(t);
			if (i.compareTo(mbase)<0) {
				BigInteger[] temp = i.divideAndRemainder(base);
				u[kval-1]=temp[0].intValue();
				return getGeneralIndexFunction(nval,mval,kval-1).apply(temp[1].longValue(),u);
			}
			BigInteger[] temp = i.subtract(mbase).divideAndRemainder(nk);
			u[kval-1]=temp[0].intValue()+mval;
			return getHornerFunction(nval,kval-1).apply(temp[1].longValue(),u);
		}		
	}

	/**
	 * A general index function on length-1 tuples.
	 * @author JHorowitz
	 *
	 */
	public static class GeneralIndexFunctionOne extends GeneralIndexFunction {
		private final int mval;
		
		/**
		 * Creates a new general index function on length-1 tuples.
		 * @param n  The size of the universe.
		 * @param m  The indices to ignore.
		 */
		public GeneralIndexFunctionOne(int n, int m) {
			super(n,m,1);
			mval=m;
		}
		
		@Override
		public int[] apply(Long t, int[] u) {
			u = new int[] {(int)(t+mval)};
			return u;
		}
		
	}
	
	/**
	 * Creates a new Horner index function.
	 * @param n  The size of the universe.
	 * @param k  The length of the index tuples.
	 * @return  The newly made Horner index function.
	 */
	public static HornerFunction makeHornerIndexFunction(int n, int k) {
		HornerFunction temp = k==1 ? new HornerFunctionOne(n) : new HornerFunction(n,k);
		hornerIndexFunctions.put(new int[] { n,  k }, temp);
		return temp;
	}
	
	/**
	 * Creates a new general index function.
	 * @param n  The size of the universe.
	 * @param m  The indices to ignore.
	 * @param k  The length of the index tuples.
	 * @return  The newly made general index function.
	 */
	public static GeneralIndexFunction makeGeneralIndexFunction(int n, int m, int k) {
		GeneralIndexFunction temp = k==1 ? new GeneralIndexFunctionOne(n,m) : new GeneralIndexFunction(n,m,k);
		generalIndexFunctions.put(new int[] { n,  m, k }, temp);
		return temp;
	}
	
	/**
	 * A Horner index function.
	 * @author Jonah Horowitz
	 *
	 */
	public static class HornerFunction implements BiFunction<Long,int[],int[]> {
		private final BigInteger base;
		private final int kval;
		private final int nval;
		
		/**
		 * Creates a new Horner index function.
		 * @param n  The size of the universe.
		 * @param k  The length of the tuples.
		 */
		public HornerFunction(int n, int k) {
			base = BigInteger.valueOf(n).pow(k-1);
			kval=k;
			nval=n;
		}

		@Override
		public int[] apply(Long t, int[] u) {
			if (u==null)
				u=new int[kval];
			BigInteger[] dm = BigInteger.valueOf(t).divideAndRemainder(base);
			u[kval-1]=dm[0].intValue();
			return getHornerFunction(nval,kval-1).apply(dm[1].longValue(),u);
		}
		
	}
	
	/**
	 * A Horner index function on length-1 tuples. 
	 * @author JHorowitz
	 *
	 */
	public static class HornerFunctionOne extends HornerFunction {
		/**
		 * Creates a new Horner index function on length-1 tuples.
		 * @param n  The size of the universe.
		 */
		public HornerFunctionOne(int n) {
			super(n,1);
		}
		
		@Override
		public int[] apply(Long t, int[] u) {
			u = new int[] {(int)(t+0)};
			return u;
		}
	}
	
	/**
	 * Retrieves the Horner index function associated with n and k.
	 * @param n  The size of the universe.
	 * @param k  The length of the tuples.
	 * @return  The existing Horner index function for n,k if it exists, a new one if it does not yet exist.
	 */
	public static HornerFunction getHornerFunction(int n, int k) {
		int[] key = new int[] { n, k };
		if (hornerIndexFunctions.containsKey(key))
			return hornerIndexFunctions.get(key);
		return makeHornerIndexFunction(n,k);
	}
	
	/**
	 * Retrieves the general index function associated with n, m, and k.
	 * @param n  The size of the universe.
	 * @param m  The indices to ignore.
	 * @param k  The length of the tuples.
	 * @return  The existing general index function for n,m,k if it exists, a new one if it does not yet exist.
	 */
	public static GeneralIndexFunction getGeneralIndexFunction(int n, int m, int k) {
		int[] key = new int[] { n, m, k };
		if (generalIndexFunctions.containsKey(key))
			return generalIndexFunctions.get(key);
		return makeGeneralIndexFunction(n,m,k);
	}
	
	/**
	 * Calculates the ith index tuple of length k with each entry less than n and at least one entry at least m.
	 * @param n  The upper limit on each entry in the tuple.
	 * @param m  The lower limit of the maximal entry in each tuple.
	 * @param k  The length of the tuple.
	 * @param i  The index from which we're generating the tuple.
	 * @param spot  The array into which to write the answer. Must be either null or of length at least k.
	 * @return  The appropriately indexed tuple.
	 */
	public static int[] makeGeneralIndexTupleWithFunctions(int n, int m, int k, long i, int[] spot) {
		if (spot==null || spot.length<k)
			spot = new int[k];
		return getGeneralIndexFunction(n,m,k).apply(i, spot);
	}
	
	/**
	 * Calculates the ith index tuple of length k with each entry less than n and at least one entry at least m.
	 * @param n  The upper limit on each entry in the tuple.
	 * @param m  The lower limit of the maximal entry in each tuple.
	 * @param k  The length of the tuple.
	 * @param i  The index from which we're generating the tuple.
	 * @param spot  The array into which to write the answer. Must be either null or of length at least k.
	 * @return  The appropriately indexed tuple.
	 */
	public static int[] makeGeneralIndexTuple(int n, int m, int k, long i, int[] spot) {
		if (spot==null || spot.length<k)
			spot = new int[k];
		if (k==1) {
			spot[0]=(int)(i+m);
			return spot;
		}
		BigInteger ell = BigInteger.valueOf(n).pow(k-1).subtract(BigInteger.valueOf(m).pow(k-1));
		BigInteger ii = BigInteger.valueOf(i);
		if (ii.compareTo(ell.multiply(BigInteger.valueOf(m)))<0) {
			BigInteger[] temp = ii.divideAndRemainder(ell);
			spot[k-1]=temp[0].intValue();
			return makeGeneralIndexTuple(n,m,k-1,temp[1].longValue(),spot);
		}
		BigInteger p = ii.subtract(ell.multiply(BigInteger.valueOf(m)));
		BigInteger[] temp = p.divideAndRemainder(BigInteger.valueOf(n).pow(k-1));
		spot[k-1]=m+temp[0].intValue();
		return Horner.hornerInv(temp[1].intValue(),n,k-1,spot);
	}
	
	/**
	 * Compares the two methods of calculating general index tuples.
	 * @param n  The size of the universe.
	 * @param m  The lower limit of the maximal entry in each tuple.
	 * @param k  The length of the tuple.
	 * @return  The runtimes of the function-based and method-based methods respectively.
	 */
	public static long[] compareMethods(int n, int m, int k) {
		int[] testArray = new int[k];
		long functionStartTime = System.nanoTime();
		for (long i = 0; i < BigInteger.valueOf(n).pow(k).subtract(BigInteger.valueOf(m).pow(k)).longValue(); i++)
			testArray = makeGeneralIndexTupleWithFunctions(n,m,k,i,testArray);
		long functionEndTime = System.nanoTime();
		testArray = new int[k];
		long methodStartTime = System.nanoTime();
		for (long i = 0; i < BigInteger.valueOf(n).pow(k).subtract(BigInteger.valueOf(m).pow(k)).longValue(); i++)
			testArray = makeGeneralIndexTuple(n,m,k,i,testArray);
		long methodEndTime = System.nanoTime();
		return new long[] { functionEndTime-functionStartTime, methodEndTime-methodStartTime };
	}
	
	public static void main(String[] args) {
		PrintStream out = null;
		try {
			out = new PrintStream("output.csv");
		} catch ( FileNotFoundException e ) {
			e.printStackTrace();
		}
		if (out==null) 
			return;
		out.println("n,m,k,function time,method time");
		for ( int n = 2; n < 51; n++ )
			for ( int m = 0; m <= n; m++ ) {
				for ( int k = 1; k < 8; k++ ) {
					String output = n+","+m+","+k;
					System.out.println(output);
					long[] times = compareMethods(n,m,k);
					output=output+","+times[0]+","+times[1];
					out.println(output);
				}
				purgeIndexFunctions();
			}
		out.close();
	}
}
