package org.uacalc.alg;

import org.uacalc.terms.*;

import java.util.*;

import org.uacalc.util.*;
import org.uacalc.alg.Closer.SGClosePowerChunk;
import org.uacalc.alg.op.*;
import java.util.concurrent.Semaphore;

import java.util.concurrent.BlockingQueue;

/**
 * A worker thread for <code>org.uacalc.alg.Closer.sgClosePowerParallel</code>
 * @author Jonah Horowitz
 *
 */
public class SGClosePowerThread extends Thread {
	public static int WAITING = 0;
	public static int RUNNING = 1;
	public static int SAFE_STOP = 2;
	
	public static final SGClosePowerChunk STOP_COMMAND = new SGClosePowerChunk(-1,new int[0]);
	public static final int SLEEP_TIME = 1000;
	
	private Semaphore statusLock = new Semaphore(1);
	private int status = WAITING;
	private BlockingQueue<SGClosePowerChunk> feeder;
	private int power;
	private int[][] opTables;
	private int algSize;
	private int[] arities;
	private int indicesPerChunk;
	private int closedMark;
	private int currentMark;
	private List<int[]> rawList;
	private List<Operation> ops;
	private HashMap<IntArray,Term> prevTermMap;
	private OperationSymbol[] symbols;
	private BlockingQueue<HashMap<IntArray,Term>> collector;
	private LinkedList<HashMap<IntArray,Term>> resultsQueue;
	private int threadNumber;

	/**
	 * Sets this thread's status
	 * @param newStatus Should take one of the values statically attached to this class.
	 */
	public void setStatus(int newStatus) {
		statusLock.acquireUninterruptibly();
		status = newStatus;
		statusLock.release();
	} // end setStatus(int)
	
	/**
	 * @return This thread's current status
	 */
	public int getStatus() {
		int temp = -1;
		statusLock.acquireUninterruptibly();
		temp = status;
		statusLock.release();
		return temp;
	} // end getStatus()
	
	/**
	 * Everything passed into this constructor should be considered read-only to avoid threading problems
	 */
	public SGClosePowerThread(BlockingQueue<SGClosePowerChunk> newFeeder, int newPower, int[][] newOpTables, int newAlgSize, 
			int[] newArities, int newIndicesPerChunk, int newClosedMark, int newCurrentMark, List<int[]> newRawList, List<Operation> newOps,
			HashMap<IntArray,Term> newPrevTermMap, OperationSymbol[] newSymbols, BlockingQueue<HashMap<IntArray,Term>> newCollector,
			int newThreadNumber) {
		super();
		feeder=newFeeder;
		power=newPower;
		opTables = newOpTables;
		algSize = newAlgSize;
		arities = newArities;
		indicesPerChunk = newIndicesPerChunk;
		closedMark = newClosedMark;
		currentMark = newCurrentMark;
		rawList = newRawList;
		ops = newOps;
		prevTermMap = newPrevTermMap;
		symbols = newSymbols;
		collector=newCollector;
		resultsQueue = new LinkedList<HashMap<IntArray,Term>>();
		threadNumber = newThreadNumber;
	} // end constructor(BlockingQueue<SGClosePowerChunk>, int, int[][], int, int[], int, int, int, List<int[]>, List<Operation>, HashMap<IntArray,Term>, OperationSymbol[], BlockingQueue<HashMap<IntArray,Term>>, int)
	
	/**
	 * Returns whether or not <code>indices</code> has an element greater than or equal to <code>min</code>
	 */
	private static boolean hasOverMin(int[] indices, int min) {
		for ( int i = 0; i < indices.length; i++ ) {
			if ( indices[i] >= min ) return true;
		} // end for 0 <= i < indices.length
		return false;
	} // end hasOverMin(int[], int)
	
	/**
	 * Concatenates two int[]'s
	 */
	private static int[] concatenateIntArrays(int[] a1, int[] a2) {
		int[] ans = new int[a1.length+a2.length];
		for ( int i = 0; i < a1.length; i++ ) {
			ans[i]=a1[i];
		} // end for 0 <= i < a1.length
		for ( int j = 0; j < a2.length; j++ ) {
			ans[a1.length+j]=a2[j];
		} // end for 0 <= j < a2.length
		return ans;
	} // end concatenateIntArrays(int[], int[])
	
	@Override
	public void run() {
		setStatus(RUNNING);
		HashMap<IntArray,Term> termMap = null;
		SGClosePowerChunk tempChunk = null;
		int arity = -1;
		int[] finalSegment = null;
		ArrayIncrementor inc = null;
		HashSet<IntArray> su = null;
		while (true) {
			if ( this.isInterrupted() ) {
				setStatus(SAFE_STOP);
				return;
			} // end if ( this.isInterrupted() )
			if ( tempChunk==null ) {
				tempChunk = feeder.poll();
				if ( tempChunk != null ) {
					if ( tempChunk == STOP_COMMAND ) break;
//					startTime = System.currentTimeMillis();
//					System.err.println("Worker thread " + threadNumber + " working on chunk " + tempChunk.toString() + ".");
					arity=arities[tempChunk.opIndex];
					finalSegment = new int[indicesPerChunk];
					su = new HashSet<IntArray>();
					termMap = new HashMap<IntArray,Term>();
					for ( int i = 0; i < indicesPerChunk; i++ ) {
						finalSegment[i]=0;
					} // end for 0 <= i < indicesPerChunk
					if ( hasOverMin(tempChunk.initialSegment,closedMark) ) {
						inc = SequenceGenerator.sequenceIncrementor(finalSegment, currentMark-1);
					} else {
						finalSegment[indicesPerChunk-1]=closedMark;
						inc = SequenceGenerator.sequenceIncrementor(finalSegment, currentMark-1, closedMark);
					} // end if-else ( hasOverMin(tempChunk.initialSegment,closedMark) )
				} else {
					arity = -1;
					finalSegment = null;
					inc = null;
					su = null;
					termMap = null;
//					startTime=-1;
					try {
						Thread.sleep(SLEEP_TIME);
					} catch ( InterruptedException e ) {						
					}
				} // end if-else ( tempChunk!=null )
			} // end if ( tempChunk==null )
			if ( tempChunk!=null ) {
				if ( tempChunk == STOP_COMMAND ) break;
				int[] vRaw = new int[power];
				int[] opTable = opTables[tempChunk.opIndex];
				int[] argIndices = concatenateIntArrays(tempChunk.initialSegment,finalSegment);
				if ( opTable != null ) {
					for ( int j = 0; j < power; j++ ) {
						int factor = algSize;
						int index = rawList.get(argIndices[0])[j];
						for ( int r = 1; r < arity; r++ ) {
							index+=factor*rawList.get(argIndices[r])[j];
							factor=factor*algSize;
						} // end for 1 <= r < arity
						vRaw[j]=opTable[index];
					} // end for 0 <= j < power
				} else {
					final Operation f = ops.get(tempChunk.opIndex);
					for ( int j = 0; j < power; j++ ) {
						final int[] arg = new int[f.arity()];
						for ( int r = 0; r < arity; r++ ) {
							arg[r]=rawList.get(argIndices[r])[j];
						} // end for 0 <= r < arity
						vRaw[j] = f.intValueAt(arg);
					} // end for 0 <= j < power
				} // end if-else ( opTable != null )
				IntArray v = new IntArray(vRaw);
				if (su.add(v)) {
					List<Term> children = new ArrayList<Term>(arity);
					for ( int r = 0; r < arity; r++ ) {
						children.add(prevTermMap.get(new IntArray(rawList.get(argIndices[r]))));
					} // end for 0 <= r < arity
					termMap.put(v,new NonVariableTerm(symbols[tempChunk.opIndex],children));
				} // end if ( su.add(v) )
			} // end if ( tempChunk!=null )
			while ( resultsQueue.size() > 0 ) {
				HashMap<IntArray,Term> presult = resultsQueue.poll();
				if ( !collector.offer(presult) ) {
					resultsQueue.addFirst(presult);
					break;
				} // end if ( !collector.offer(presult) )
			} // end while ( resultsQueue.size() > 0 )
			if ( tempChunk!=null && !inc.increment() ) {
				tempChunk=null;
//				status.addChunk(System.currentTimeMillis()-startTime);
				if ( !collector.offer(termMap) ) {
					resultsQueue.add(termMap);
				} else {
					termMap = null;
				} // end if-else ( !collector.offer(termMap) )
			} // end if ( tempChunk!=null && !inc.increment() )
		} // end while (true)
		HashMap<IntArray,Term> completed = new HashMap<IntArray,Term>();
		completed.put(new IntArray(new int[] {threadNumber}), null);
		while ( !collector.offer(completed) ) {
			try {
				Thread.sleep(SLEEP_TIME);
			} catch ( InterruptedException e ) {
				System.err.println("Worker thread " + threadNumber + " was interrupted while sleeping.");
				break;
			}
		}
		setStatus(SAFE_STOP);
	} // end run()

} // end class SGClosePowerThread
