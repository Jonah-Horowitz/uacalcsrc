package org.uacalc.alg;

import java.util.*;
import org.uacalc.util.*;
import org.uacalc.terms.*;
import org.uacalc.alg.op.*;
import java.util.concurrent.BlockingQueue;
import org.uacalc.eq.*;

/**
 * A worker thread for <code>org.uacalc.alg.Closer2.onePassParallel</code>
 * @author Jonah Horowitz
 */
public class SGCloseThread extends SGClosePowerThread {
	
	public SGCloseThread(BlockingQueue<SGClosePowerChunk> newFeeder, int[][] newOpTables, int[] newArities, int newArgumentsPerChunk, 
			int newClosedMark, int newCurrentMark, List<int[]> newRawList, List<Operation> newOps, HashMap<IntArray,Term> newPrevTermMap, 
			OperationSymbol[] newSymbols, BlockingQueue<SGClosePowerResult> newCollector, int newThreadNumber, int[][] newImgOpTables, 
			HashMap<IntArray,Integer> newPrevHomomorphism, int newImgAlgSize) {
		super(newFeeder,1,newOpTables,-1,newArities,newArgumentsPerChunk,newClosedMark,newCurrentMark,newRawList,newOps,newPrevTermMap,newSymbols,newCollector,newThreadNumber, newImgOpTables, newPrevHomomorphism, newImgAlgSize);
	} // end constructor(BlockingQueue<SGClosePowerChunk>, int, int, int, List<int[]>, List<Operation>, HashMap<IntArray,Term>, BlockingQueue<HashMap<IntArray,Term>>, int) 
	
	@Override
	public void run() {
		setStatus(RUNNING);
		HashMap<IntArray,Term> termMap = null;
		SGClosePowerChunk tempChunk = null;
		int arity = -1;
		int[] finalSegment = null;
		ArrayIncrementor inc = null;
		HashSet<IntArray> su = null;
		Operation f = null;
		HashMap<IntArray,Integer> morphism = null;
		Equation failingEquation = null;
		while (true) {
			if (this.isInterrupted()) {
				setStatus(SAFE_STOP);
				return;
			} // end if (this.isInterrupted())
			if (tempChunk==null) {
				tempChunk = feeder.poll();
				if (tempChunk!=null) {
					if (tempChunk==STOP_COMMAND) break;
					f=ops.get(tempChunk.opIndex);
					arity=f.arity();
					finalSegment=new int[indicesPerChunk];
					su = new HashSet<IntArray>();
					termMap = new HashMap<IntArray,Term>();
					morphism = prevHomomorphism==null?null:new HashMap<IntArray,Integer>();
					failingEquation=null;
					for ( int i = 0; i < indicesPerChunk; i++ ) finalSegment[i]=0;
					if (hasOverMin(tempChunk.initialSegment,closedMark)) {
						inc = SequenceGenerator.sequenceIncrementor(finalSegment, currentMark-1);
					} else {
						finalSegment[indicesPerChunk-1]=closedMark;
						inc = SequenceGenerator.sequenceIncrementor(finalSegment, currentMark-1, closedMark);
					} // end if-else (hasOverMin(tempChunk.initialSegment,closedMark))
				} else {
					f=null;
					arity=-1;
					finalSegment=null;
					inc=null;
					su=null;
					termMap=null;
					morphism=null;
					failingEquation=null;
					try {
						Thread.sleep(SLEEP_TIME);
					} catch ( InterruptedException e ) {}
				} // end if-else (tempChunk!=null)
			} // end if (tempChunk==null)
			if (tempChunk!=null) {
				if (tempChunk==STOP_COMMAND) break;
				int[] argIndices = concatenateIntArrays(tempChunk.initialSegment,finalSegment);
				int[][] arg = new int[arity][];
				for ( int i = 0; i < arity; i++ ) arg[i]=rawList.get(argIndices[i]);
				int[] vRaw = f.valueAt(arg);
				IntArray v = new IntArray(vRaw);
				if ( !prevTermMap.containsKey(v) && su.add(v) ) {
					List<Term> children = new ArrayList<Term>(arity);
					for ( int r = 0; r < arity; r++ ) children.add(prevTermMap.get(new IntArray(rawList.get(argIndices[r]))));
					termMap.put(v, new NonVariableTerm(f.symbol(),children));
					if ( prevHomomorphism!=null ) {
						final int[] args = new int[arity];
						for ( int t = 0; t < arity; t++ ) args[t] = prevHomomorphism.get(new IntArray(rawList.get(argIndices[t])));
						morphism.put(v, imgOpTables[tempChunk.opIndex][Horner.horner(args, imgAlgSize)]);
					} // end if ( prevHomomorphism!=null )
				} else {
					if ( prevHomomorphism!=null ) {
						final int[] args = new int[arity];
						for ( int t = 0; t < arity; t++ ) args[t] = prevHomomorphism.get(new IntArray(rawList.get(argIndices[t])));
						int v2 = prevHomomorphism.containsKey(v)?prevHomomorphism.get(v):morphism.get(v);
						if ( v2!=imgOpTables[tempChunk.opIndex][Horner.horner(args, imgAlgSize)] ) {
							List<Term> children = new ArrayList<Term>(arity);
							for ( int r = 0; r < arity; r++ ) children.add(prevTermMap.get(new IntArray(rawList.get(argIndices[r]))));
							failingEquation = new Equation(prevTermMap.containsKey(v)?prevTermMap.get(v):termMap.get(v), new NonVariableTerm(symbols[tempChunk.opIndex],children));
						} // end if ( v2!=imgOpTables[tempChunk.opIndex][Horner.horner(args, imgAlgSize)] )
					} // end if ( prevHomomorphism!=null )
				} // end if-else ( !prevTermMap.containsKey(v) && su.add(v) )
			} // end if (tempChunk!=null)
			while (resultsQueue.size()>0) {
				SGClosePowerResult presult = resultsQueue.poll();
				if (!collector.offer(presult)) {
					resultsQueue.addFirst(presult);
					break;
				} // end if (!collector.offer(presult))
			} // end while (resultsQueue.size()>0)
			if (tempChunk!=null && !inc.increment()) {
				tempChunk=null;
				SGClosePowerResult tempRes = new SGClosePowerResult(termMap,morphism,failingEquation);
				if (!collector.offer(tempRes)) {
					resultsQueue.add(tempRes);
				} // end if (!collector.offer(termMap))
				termMap = null;
				morphism = null;
			} // end if (tempChunk!=null && !inc.increment())
		} // end while (true)
		SGClosePowerResult completed = new SGClosePowerResult(threadNumber);
		while (!collector.offer(completed)) {
			try {
				Thread.sleep(SLEEP_TIME);
			} catch ( InterruptedException e ) {
				System.err.println("Worker thread "+threadNumber+" was interrupted while sleeping.");
				break;
			} // end try-catch InterruptedException
		} // end while (!collector.offer(completed))
		setStatus(SAFE_STOP);
	} // end run()
} // end class SGCloseThread
