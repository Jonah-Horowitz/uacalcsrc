package org.uacalc.alg;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.locks.*;

import org.uacalc.util.*;
import org.uacalc.terms.*;
import org.uacalc.eq.*;
import org.uacalc.alg.op.*;
import org.uacalc.ui.tm.ProgressReport;

import java.util.concurrent.LinkedBlockingQueue;

/**
 * A new version of <code>org.uacalc.alg.CLoser</code>, mostly just the same code divided up differently.
 * @author Jonah Horowitz
 *
 */
public class Closer2 {
	public static final Integer MINUS_ONE = new Integer(-1);
	public static final int SERIAL = 0;
	public static final int PARALLEL = 1;
	public static final int EQUAL_WORKLOAD = 2;
	public static final int PROGRAM_CHOICE = -1;
	
	public static int FEEDER_CAPACITY=100000; // Maximum number of chunks the feeder queue can hold
	public static int THREAD_PRIORITY=Thread.NORM_PRIORITY; // Priority of the worker/feeder threads
	public static int MAX_UNUSED_PASSES=100; // Maximum number of consecutive passes the collector thread can go idle before taking a nap
	public static int PROCESS_PER_LOOP=1000; // How many partial results the collector thread should process per loop
	
	private Algebra algebra; // The algebra with respect to which we are closing
	private List<IntArray> ans = null; // Eventually, the subuniverse itself
	private boolean completed = false; // Whether or not we are done computing
	private List<IntArray> generators; // The generator list which we will be closing
	private Map<IntArray,Term> termMap = null; // A map from operations to terms, with generators mapped to distinct variables
	private IntArray eltToFind = null; // A specific element being sought
	private List<IntArray> eltsToFind = null; // A list of elements being sought
	private Map<IntArray,Integer> indicesMapOfFoundElts = null; // The locations of found elements
	private boolean allEltsFound = false; // Whether or not we have found all sought elements
	private int specialEltsFound = 0; // How many special elements we have found
	private SmallAlgebra imageAlgebra = null; // The image of a sought homomorphism
	private Map<IntArray,Integer> homomorphism = null; // A partial homomorphism from algebra to imageAlgebra
	private Equation failingEquation = null; // A list of two terms
	private SmallAlgebra rootAlgebra = null; // The root of a power algebra
	private List<Operation> operations = null; // A list of operations on the root algebra; to test if they are in the clone
	private Map<Operation,Term> termMapForOperations = null; // A term map for <code>org.uacalc.alg.op.Operation</code>s
	private int[][] blocks = null; // A blocks and values constraint as in intArray (?)
	private int[][] values = null;
	private int maxSize=-1; // Stop closing if we have found this many elements
	private ProgressReport report = null; // To where we should be reporting progress data
	private boolean suppressOutput = false; // Whether or not to suppress output
	private int passDecisionProcedure = PROGRAM_CHOICE; // How to decide which method to use to calculate each pass
	private int numThreads = 0; // Number of threads to use in calculation (0 = number of cores)
	private boolean splitFeederThread = false; // Whether or not to separate the data stream from the reducer in parallel mode 
	private int argumentsPerChunk = 1; // In parallel mode, determines how many arguments are allocated per chunk of data
	private boolean forceNonPower = false; // if true, does not use the special algorithm for power algebras
	
	private boolean stopEachPass=false; // Only used for testing 
	
	public Closer2( Algebra alg, List<IntArray> gens ) {
		algebra = alg;
		setGenerators(gens);
	} // end constructor( BigProductAlgebra, List<IntArray> )
	
	public Closer2( Algebra alg, List<IntArray> gens, Map<IntArray,Term> termMap ) {
		this(alg,gens);
		this.termMap=termMap;
	} // end constructor(BigProductAlgebra, List<IntArray>, Map<IntArray,Term>)
	
	public Closer2( Algebra alg, List<IntArray> gens, boolean makeTermMap ) {
		this(alg,gens);
		if (makeTermMap) setupTermMap();
	} // end constructor(BigProductAlgebra, List<IntArray>, boolean)
	
	private void setupTermMap() {
		termMap = new HashMap<IntArray,Term>();
		if (generators.size() == 1) termMap.put(generators.get(0), Variable.x);
		if (generators.size() == 2) {
			termMap.put(generators.get(0), Variable.x);
			termMap.put(generators.get(1), Variable.y);
		} // end if ( generators.size() == 2 )
		if (generators.size() == 3) {
			termMap.put(generators.get(0), Variable.x);
			termMap.put(generators.get(1), Variable.y);
			termMap.put(generators.get(2), Variable.z);
		} // end if ( generators.size() == 3 )
		int k = 0;
		if (generators.size() > 3) {
			for (Iterator<IntArray> it = generators.iterator(); it.hasNext(); k++) {
				Variable var = new VariableImp("x_" + k);
				termMap.put(it.next(), var);
			} // end for (Iterator<IntArray> it = generators.iterator(); it.hasNext(); k++)
		} // end if (generators.size() > 3)
	} // end setupTermMap()
	
	public List<IntArray> getGenerators() { return generators; }	
	public List<IntArray> getAnswer() { return ans; }
	public Equation getFailingEquation() { return failingEquation; }
	public Map<Operation,Term> getTermMapForOperations() { return termMapForOperations; }	
	public Closer2 setRootAlgebra(SmallAlgebra alg) { rootAlgebra = alg; return this; }	
	public Closer2 setOperations(List<Operation> ops) { operations=ops; return this; }
	public Map<IntArray,Term> getTermMap() { return termMap; }
	public Closer2 setTermMap(Map<IntArray,Term> tm) { termMap=tm; return this; }
	public SmallAlgebra getImageAlgebra() { return imageAlgebra; }
	public Map<IntArray,Integer> getHomomorphism() { return homomorphism; }
	public Closer2 setHomomorphism(Map<IntArray,Integer> morphism) { homomorphism=morphism; return this; }
	public IntArray getElementToFind() { return eltToFind; }
	public Closer2 setElementToFind(IntArray e) { eltToFind=e; return this; }
	public List<IntArray> getElementsToFind() { return eltsToFind; }
	public boolean allElementsFound() { return allEltsFound; }
	public int[][] getBlocks() { return blocks; }
	public Closer2 setBlocks(int[][] newBlocks) { blocks=newBlocks; return this; }
	public int[][] getValues() { return values; }
	public Closer2 setValues(int[][] newValues) { values=newValues; return this; }
	public int getMaxSize() { return maxSize; }
	public Closer2 setMaxSize(int size) { maxSize=size; return this; }
	public Closer2 setProgressReport(ProgressReport newReport) { report=newReport; return this; }
	public boolean isSuppressOutput() { return suppressOutput; }
	public Closer2 setSuppressOutput(boolean newVal) { suppressOutput=newVal; return this; }
	public Closer2 setPassDecisionProcedure(int n) { passDecisionProcedure=n; return this; }
	public int getPassDecisionProcedure() { return passDecisionProcedure; }
	public Closer2 setNumThreads(int threads) { numThreads=threads; return this; }
	public int getNumThreads() { return numThreads; }
	public Closer2 setSplitFeederThread(boolean split) { splitFeederThread=split; return this; }
	public boolean getSplitFeederThread() { return splitFeederThread; }
	public Closer2 setArgumentsPerChunk(int args) { argumentsPerChunk=args; return this; }
	public int getArgumentsPerChunk() { return argumentsPerChunk; }
	public int getPass() { return pass; }
	public Closer2 setStopEachPass(boolean val) { stopEachPass=val; return this; }
	public boolean getStopEachPass() { return stopEachPass; }
	public boolean getCompleted() { return completed; }
	public Closer2 setForceNonPower(boolean newVal) { forceNonPower = newVal; return this; }
	
	public Closer2 setGenerators(List<IntArray> gens) {
		if ( gens==null ) return this;
		generators = new ArrayList<IntArray>(gens.size());
		final Set<IntArray> hs = new HashSet<IntArray>(gens.size());
		for ( IntArray ia : gens ) {
			if (hs.add(ia)) generators.add(ia);			
		} // end for ( IntArray ia : gens )
		return this;
	} // end setGenerators(List<IntArray>)
	
	public Closer2 setImageAlgebra(SmallAlgebra alg) {
		if (!alg.similarityType().equals(algebra.similarityType())) throw new IllegalArgumentException("The algebras must be similar.");
		imageAlgebra=alg;
		return this;
	} // end setImageAlgebra(SmallAlgebra)
	
	public Closer2 setHomomorphism(int[] algGens) {
		if ( algGens.length!=generators.size()) throw new IllegalArgumentException("Wrong number of generators.");
		Map<IntArray,Integer> homo = new HashMap<IntArray,Integer>(generators.size());
		int k = 0;
		for ( IntArray g : generators ) {
			homo.put(g, algGens[k++]);
		} // end for ( IntArray g : generators )
		homomorphism=homo;
		return this;
	} // end setHomomorphism(int[])
	
	public Closer2 setElementsToFind(List<IntArray> e, List<IntArray> gens) {
		setGenerators(gens);
		return setElementsToFind(e);
	} // end setElementsToFind(List<IntArray>, List<IntArray>)
	
	public Closer2 setElementsToFind(List<IntArray> e) {
		eltsToFind=e;
		indicesMapOfFoundElts = new HashMap<IntArray,Integer>(e.size());		
		for ( IntArray ia : e ) {
			indicesMapOfFoundElts.put(ia, MINUS_ONE);
		} // end for ( IntArray ia : e )
		for ( int i = 0; i < generators.size(); i++ ) {
			if ( MINUS_ONE.equals(indicesMapOfFoundElts.get(generators.get(i))) ) {
				indicesMapOfFoundElts.put(generators.get(i), new Integer(i));
				specialEltsFound++;
			} // end if ( MINUS_ONE.equals(indicesMapOfFoundElts.get(generators.get(i))) )
		} // end for 0 <= i < generators.size()
		return this;
	} // end setElementsToFind(List<IntArray>)
	
	private CloserTiming timing=null; // Timing tracker
	private int pass; // Which pass number we're currently calculating
	private int numOfOps; // The number of operations in the base algebra
	private int closedMark=0; // The point in ans to which we have already closed
	private int currentMark=-1; // The point in ans to which we will close this pass
	private Operation[] imgOps = null; // Operations in the imageAlgebra
	private List<int[]> rawList; // The raw list of subuniverse elements
	private HashSet<IntArray> su; // The set of all subuniverse elements
	private int operationsFound; // The number of operations already found
	private int algSize; // The size of the factor algebra
	private List<Operation> ops; // Operations of the factor algebra
	private int[][] opTables; // Operation tables of the factor algebra
	private OperationSymbol[] symbols; // Operation symbols of the factor algebra
	private int[] arities; // The arities of the operations of the factor algebra
	private int power; // The number of factors in a power algebra
	private int[][] imgOpTables; // The operation tables of the image algebra
	private int imgAlgSize;
	
	private void initializeClosure() {
		if ( report!=null ) report.addStartLine("subpower closing...");
		numOfOps=algebra.operations().size();
		if ( homomorphism!=null ) {
			imgOps=new Operation[numOfOps];
			imageAlgebra.makeOperationTables();
			for ( int i = 0; i < numOfOps; i++ ) imgOps[i]=imageAlgebra.getOperation(algebra.operations().get(i).symbol());
			imgAlgSize=imageAlgebra.cardinality();
			imgOpTables = new int[numOfOps][];
			for ( int i = 0; i < numOfOps; i++ ) {
				Operation op = imageAlgebra.getOperation(algebra.operations().get(i).symbol());
				if ( op instanceof OperationWithDefaultValue ) {
					imgOpTables[i]=((OperationWithDefaultValue) op).getTotalTable();
				} else {
					imgOpTables[i]=op.getTable();
				} // end if-else ( op instanceof OperationWithDefaultValue )
			} // end for 0 <= i < numOfOps
		} // end if ( homomorphism!=null )
		opTables = new int[numOfOps][];
		symbols = new OperationSymbol[numOfOps];
		arities = new int[numOfOps];
		ops = algebra.operations();
		for ( int i = 0; i < numOfOps; i++ ) {
			Operation op = ops.get(i);
			if ( op instanceof OperationWithDefaultValue ) {
				opTables[i] = ((OperationWithDefaultValue) op).getTotalTable();
			} else {
				opTables[i] = op.getTable();
			} // end if-else ( op instanceof OperationWithDefaultValue )
			arities[i]=op.arity();
			symbols[i]=op.symbol();
		} // end for 0 <= i < numOfOps
		if (ans==null || ans.size()==0) ans=new ArrayList<IntArray>(generators);
		pass=0;
		operationsFound=0;
		rawList=new ArrayList<int[]>();
		for ( IntArray ia : generators ) {
			rawList.add(ia.getArray());
		} // end for ( IntArray ia : generators )
		su = new HashSet<IntArray>(ans);
		for ( Operation op : ops ) {
			if ( op.arity()==0 ) {
				IntArray ia = (IntArray)op.valueAt(new ArrayList<IntArray>());
				if (su.add(ia)) {
					ans.add(ia);
					rawList.add(ia.getArray());
					if (termMap!=null) termMap.put(ia, NonVariableTerm.makeConstantTerm(op.symbol()));
				} // end if (su.add(ia))
			} // end if (op.arity()==0)
		} // end for ( Operation op : ops )
/*		final List<IntArray> constants = algebra.getConstants();
		for ( IntArray arr : constants ) {
			if (su.add(arr)) {
				ans.add(arr);
				rawList.add(arr.getArray());
				if (termMap!=null) termMap.put(arr, NonVariableTerm.makeConstantTerm(algebra.constantToSymbol.get(arr)));
			} // end if (su.add(arr))
		} // end for ( IntArray arr : constants )/**/
		currentMark=ans.size();
		if (report!=null) timing = new CloserTiming(algebra, report);
	} // end initializeClosure()
		
	public List<IntArray> sgClose( List<IntArray> elems, int newClosedMark, Map<IntArray,Term> tM ) {
		ans=new ArrayList<IntArray>(elems);
		closedMark=newClosedMark;
		termMap=tM;
		return sgClose();
	} // end sgClose(List<IntArray>, int, Map<IntArray,Term>)
	
	public List<IntArray> sgClose() {
		if ( !forceNonPower && (algebra instanceof BigProductAlgebra) && ((BigProductAlgebra)algebra).isPower() ) {
			((BigProductAlgebra)algebra).rootFactors().get(0).makeOperationTables();
			return sgClosePower();
		} // end if ( algebra.isPower() )	
		
		if (pass==0) initializeClosure();
		
		while ( closedMark<currentMark ) {
			if ( report!=null ) {
				timing.updatePass(ans.size());
				String str="pass: "+pass+" size: "+ans.size();
				report.setPass(pass);
				report.setPassSize(ans.size());
				if (!suppressOutput) report.addLine(str);
			} // end if ( report!=null )
			pass++;
			boolean result = false;
			switch (currentPassType()) {
				case SERIAL: result = onePassSerial(); break;
				case PARALLEL: result = onePassParallel(); break;
				case EQUAL_WORKLOAD: result = onePassEqualWorkload(); break;
			} // end switch (currentPassType())
			if (!result) return completed?ans:null;
			closedMark=currentMark;
			currentMark=ans.size();
			if (imgOps==null && algebra.cardinality()>0 && currentMark>=algebra.cardinality()) {
				completed = true;
				break;
			} // end if (imgOps==null && algebra.cardinality()>0 && currentMark>=algebra.cardinality())
			if (stopEachPass) break;
		} // end while ( closedMark<currentMark )
		if ( closedMark>=currentMark ) completed=true;
		return ans;/**/
	} // end sgClose()
	
	/**
	 * Determines which method should be used to calculate the upcoming pass
	 */
	public int currentPassType() {
		if ( passDecisionProcedure!=PROGRAM_CHOICE ) return passDecisionProcedure;
		int nt = numThreads==0?Runtime.getRuntime().availableProcessors():numThreads;		
		if ( nt==1 ) return SERIAL;
		return PARALLEL;
	} // end currentPassType()
	
	public boolean onePassSerial() {
		final boolean reportNotNull = report!=null;
		final boolean imgAlgNull = imgOps==null;
		final boolean eltToFindNotNull = eltToFind!=null;
		final boolean eltsToFindNotNull = eltsToFind!=null;
		final boolean operationsNotNull = operations!=null;
		
		for ( int i = 0; i < numOfOps; i++) {
			Operation f = algebra.operations().get(i);
			final int arity = f.arity();
			if (arity==0) continue;
			int[] argIndices=new int[arity];
			for ( int j = 0; j < arity; j++ ) argIndices[j]=0;
			argIndices[arity-1]=closedMark;
			ArrayIncrementor inc = SequenceGenerator.sequenceIncrementor(argIndices, currentMark-1, closedMark);
			final int[][] arg = new int[arity][];
			while (true) {
				if (Thread.currentThread().isInterrupted()) {
					if (reportNotNull) {
						report.addEndingLine("cancelled...");
						report.setSize(ans.size());
					} // end if (reportNotNull)
					return false;
				} // end if (Thread.currentThread().isInterrupted())
				
				for ( int j = 0; j < arity; j++ ) {
					arg[j]=rawList.get(argIndices[j]);
				} // end for 0 <= j < arity
				
				int[] vRaw = f.valueAt(arg);
				IntArray v = new IntArray(vRaw);
				if (reportNotNull) timing.incrementApps();
				
				if ( su.add(v) ) {
					ans.add(v);
					rawList.add(vRaw);
					if (reportNotNull) {
						timing.incrementNextPassSize();
						report.setSize(ans.size());
					} // end if (reportNotNull)
					if (termMap!=null) {
						List<Term> children = new ArrayList<Term>(arity);
						for ( int j = 0; j < arity; j++ ) children.add(termMap.get(ans.get(argIndices[j])));
						termMap.put(v, new NonVariableTerm(f.symbol(), children));
						if (operationsNotNull) {
							Term term = termMap.get(v);
							List<Variable> vars = new ArrayList<Variable>(generators.size());
							for ( IntArray ia : generators ) vars.add((Variable)termMap.get(ia));
							Operation termOp = term.interpretation(rootAlgebra, vars, true);
							for ( Operation op : operations ) {
								if ( termMapForOperations.containsKey(op) && Operations.equalValues(termOp, op) ) {
									termMapForOperations.put(op, term);
									operationsFound++;
									if ( operationsFound==operations.size() ) {
										completed=true;
										return false;
									} // end if ( operationsFound==operations.size() )
								} // end if ( termMapForOperations.containsKey(op) && Operations.equalValues(termOp, op) )
							} // end for ( Operation op : operations )
						} // end if (operationsNotNull)
					} // end if (termMap!=null)
					if ( eltToFindNotNull && v.equals(eltToFind) ) {
						if (reportNotNull) report.addEndingLine("closing done, found "+eltToFind+", at "+ans.size());
						completed=true;
						return false;
					} // end if ( eltToFindNotNull && v.equals(eltToFind) )
					if ( eltsToFindNotNull && MINUS_ONE.equals(indicesMapOfFoundElts.get(v)) ) {
						final int index = ans.size()-1;
						indicesMapOfFoundElts.put(v, index);
						specialEltsFound++;
						if (reportNotNull) report.addLine("found "+v+" at "+index);
						if ( specialEltsFound==eltsToFind.size() ) {
							if (reportNotNull) report.addEndingLine("closing done, found all "+eltsToFind.size()+" elements.");
							allEltsFound=true;
							completed=true;
							return false;
						} // end if ( specialEltsFound==eltsToFind.size() )
					} // end if ( eltsToFindNotNull && MINUS_ONE.equals(indicesMapOfFoundElts.get(v)) )
					if (imgAlgNull) {
						if ( algebra.cardinality()>0 && ans.size()==algebra.cardinality() ) {
							if (reportNotNull) {
								report.addEndingLine("found all "+ans.size()+" elements");
								report.setSize(ans.size());
							} // end if (reportNotNull)
							completed=true;
							return false;
						} // end if ( algebra.cardinality()>0 && ans.size()==algebra.cardinality() )
					} else {
						final int[] args = new int[arity];
						for ( int t = 0; t < arity; t++ ) args[t]=homomorphism.get(ans.get(argIndices[t]));
						homomorphism.put(v, imgOps[i].intValueAt(args));
					} // end if-else (imgAlgNull)
				} else {
					if ( imgOps!=null ) {
						final int[] args=new int[arity];
						for ( int t = 0; t < arity; t++ ) args[t]=homomorphism.get(ans.get(argIndices[t]));
						if ( homomorphism.get(v).intValue() != imgOps[i].intValueAt(args) ) {
							List<Term> children = new ArrayList<Term>(arity);
							for ( int r = 0; r < arity; r++ ) children.add(termMap.get(ans.get(argIndices[r])));
							failingEquation = new Equation( termMap.get(v), new NonVariableTerm(imgOps[i].symbol(),children) );
							if (reportNotNull) {
								report.setSize(ans.size());
								report.addEndingLine("failing equation:\n"+failingEquation);
							} // end if (reportNotNull)
							completed=true;
							return false;
						} // end if ( homomorphism.get(v).intValue() != imgOps.get(i).intValueAt(args) )
					} // end if ( imgOps!=null )
				} // end if-else ( su.add(v) )
				if (!inc.increment()) break;
			} // end while (true)
		} // end for 0 <= i < numOfOps
		return true;
	} // end onePassSerial
	
	public boolean onePassParallel() {
		final long passStartTime = System.currentTimeMillis();
		final boolean reportNotNull = report!=null;
		final boolean eltToFindNotNull = eltToFind!=null;
		final boolean eltsToFindNotNull = eltsToFind!=null;
		final boolean operationsNotNull = operations!=null;
		final int numWorkers = Math.max((numThreads==0?Runtime.getRuntime().availableProcessors():numThreads)-(splitFeederThread?2:1),1);
		int unusedPasses = 0;
		final LinkedBlockingQueue<SGClosePowerThread.SGClosePowerChunk> feeder = new LinkedBlockingQueue<SGClosePowerThread.SGClosePowerChunk>(FEEDER_CAPACITY);
		final LinkedBlockingQueue<SGClosePowerThread.SGClosePowerResult> collector = new LinkedBlockingQueue<SGClosePowerThread.SGClosePowerResult>();
		SGCloseThread[] workers = new SGCloseThread[numWorkers];
		boolean[] workersFinished = new boolean[numWorkers];
		HashMap<IntArray,Term> prevTermMap = new HashMap<IntArray,Term>();
		prevTermMap.putAll(termMap);
		List<int[]> prevRawList = new ArrayList<int[]>(rawList);
		HashMap<IntArray,Integer> prevHomomorphism = null;
		if ( imgOps!=null ) {
			prevHomomorphism = new HashMap<IntArray,Integer>();
			prevHomomorphism.putAll(homomorphism);
		} // end if ( imgOps!=null )
		final List<ReentrantLock> opLocks = new ArrayList<ReentrantLock>();
		for ( int i = 0; i < ops.size(); i++ ) opLocks.add(new ReentrantLock());
		for ( int i = 0; i < numWorkers; i++ ) {
			workers[i]=new SGCloseThread(feeder,opTables,arities,argumentsPerChunk,closedMark,currentMark,prevRawList,ops,prevTermMap,symbols,collector,i,imgOpTables,prevHomomorphism,imgAlgSize,opLocks);
			workers[i].setPriority(THREAD_PRIORITY);
			workersFinished[i]=false;
			workers[i].start();
		} // end for 0 <= i < numWorkers
		SGClosePowerThread.SGClosePowerResult partResult = null;
		long chunksProcessedThisPass=0;
		long totalChunks = 0;
		for ( int i = 0; i < numOfOps; i++ ) {
			int addendum = 1;
			for ( int j = 0; j < arities[i]-argumentsPerChunk; j++ ) addendum *= currentMark;
			totalChunks+=addendum;
		} // end for 0 <= i < numOfOps
		long totalElements = 0;
		for ( int i = 0; i < numOfOps; i++ ) {
			int addendum = 1;
			for ( int j = 0; j < arities[i]; j++ ) addendum *= currentMark;
			totalElements+=addendum;
		} // end for 0 <= i < numOfOps
		final int[] arities = new int[ops.size()];
		for ( int i = 0; i < ops.size(); i++ ) arities[i]=ops.get(i).arity();
		SGFeederRunner feederRunner = new SGFeederRunner(feeder,numWorkers);
		Thread feederThread = null;
		if (splitFeederThread) {
			feederThread = new Thread(feederRunner);
			feederThread.start();
		} // end if (splitFeederThread)
		
		while (true) {
			// Check for task cancellation
			if (Thread.currentThread().isInterrupted()) {
				killThreads(workers,feederThread);
				if (reportNotNull) {
					report.setSize(ans.size());
					report.addEndingLine("cancelled...");
				} // end if (reportNotNull)
				return false;
			} // end if (Thread.currentThread().isInterrupted())
			
			// Feed the queue if necessary
			if (!splitFeederThread) {
				feederRunner.fillQueue();
				if (!feederRunner.hasMore() && feeder.remainingCapacity()>=numWorkers) for ( int i = 0; i < numWorkers; i++ ) feeder.offer(SGClosePowerThread.STOP_COMMAND);
			} // end if (!splitFeederThread)
		
			// Counting sheep
			if ( collector.size()==0 ) {
				unusedPasses++;
			} else {
				unusedPasses=0;
			} // end if-else ( collector.size()==0 )
			if ( unusedPasses>=MAX_UNUSED_PASSES ) {
				try {
					Thread.sleep(SGClosePowerThread.SLEEP_TIME);
				} catch ( InterruptedException e ) {}
				unusedPasses=0;
			} // end if ( unusedPasses>=MAX_UNUSED_PASSES )

			for ( int q = 0; q < PROCESS_PER_LOOP; q++ ) {
				if (collector.size()==0) break;
				partResult=collector.poll();
				if ( partResult!=null && partResult.completed>=0 ) {
					workersFinished[partResult.completed]=true;
				} else if ( partResult!=null ) {
					chunksProcessedThisPass++;
					if ( partResult.failingEquation!=null && homomorphism!=null ) {
						failingEquation=partResult.failingEquation;
						if (reportNotNull) {
							report.setSize(ans.size());
							report.addEndingLine("failing equation:\n"+failingEquation);
						} // end if (reportNotNull)
						completed=true;
						killThreads(workers,feederThread);
						return false;
					} // end if ( partResult.failingEquation!=null && homomorphism!=null )
					List<IntArray> partAns = new ArrayList<IntArray>(partResult.termMap.keySet());					
					for ( IntArray v : partAns ) {
						if (su.add(v)) {
							ans.add(v);
							rawList.add(v.getArray());
							if (termMap!=null) {
								termMap.put(v, partResult.termMap.get(v));
								if (operationsNotNull) {
									Term term = partResult.termMap.get(v);
									List<Variable> vars = new ArrayList<Variable>(generators.size());
									for ( IntArray ia : generators ) vars.add((Variable)termMap.get(ia));
									Operation termOp = term.interpretation(rootAlgebra, vars, true);
									for ( Operation op : operations ) {
										if (Operations.equalValues(termOp, op)) {
											termMapForOperations.put(op, term);
											operationsFound++;
											if (operationsFound==operations.size()) {
												completed = true;
												killThreads(workers,feederThread);
												return false;
											} // end if (operationsFound==operations.size()
										} // end if (Operations.equalValues(termOp, op))
									} // end for ( Operation op : operations )
								} // end if (operationsNotNull)
							} // end if (termMap!=null)
							if ( eltToFindNotNull && v.equals(eltToFind) ) {
								if (reportNotNull) {
									report.setSize(ans.size());
									report.addEndingLine("Closing done, found "+v+", at "+ans.size());
								} // end if (reportNotNull)
								completed=true;
								killThreads(workers,feederThread);
								return false;
							} // end if ( eltToFindNotNull && v.equals(eltToFind) )
							if ( eltsToFindNotNull && MINUS_ONE.equals(indicesMapOfFoundElts.get(v)) ) {
								final int index = ans.size()-1;
								indicesMapOfFoundElts.put(v, index);
								specialEltsFound++;
								if (reportNotNull) report.addLine("Found "+v+", at "+index);
								if ( specialEltsFound==eltsToFind.size() ) {
									if (reportNotNull) report.addEndingLine("Closing done, found all "+specialEltsFound+" elements.");
									allEltsFound=true;
									completed=true;
									killThreads(workers,feederThread);
									return false;
								} // end if ( specialEltsFound==eltsToFind.size() )
							} // end if ( eltsToFindNotNull && MINUS_ONE.equals(indicesMapOfFoundElts.get(v)) )
							if ( imageAlgebra==null ) {
								final int size = ans.size();
								if ( algebra.cardinality()>0 && size==algebra.cardinality() ) {
									if (reportNotNull) {
										report.setSize(size);
										report.addEndingLine("Found all "+size+" elements");
									} // end if (reportNotNull)
									completed=true;
									killThreads(workers,feederThread);
									return false;
								} // end if ( algebra.cardinality>0 && size==algebra.cardinality() )
							} else {
								homomorphism.put(v, partResult.homomorphism.get(v));
							} // end if-else ( imageAlgebra==null )
						} else {
							if ( imageAlgebra!=null ) {
								if ( homomorphism.get(v).intValue()!=partResult.homomorphism.get(v).intValue() ) {
									failingEquation = new Equation(termMap.get(v), partResult.termMap.get(v));
									if (reportNotNull) {
										report.setSize(ans.size());
										report.addEndingLine("failing equation:\n"+failingEquation);
									} // end if (reportNotNull)
									completed=true;
									killThreads(workers,feederThread);
									return false;
								} // end if ( homomorphism.get(v).intValue()!=partResult.homomorphism.get(v).intValue() )
							} // end if ( imageAlgebra!=null )
						} // end if-else (su.add(v))
					} // end for ( IntArray v : partAns )
				} // end else if ( partResult!=null )
			} // end for 0 <= q < PROCESS_PER_LOOP
			
			// Check for dead workers, print any stack traces to the error stream and notify the user
			for ( int i = 0; i < numWorkers; i++ ) {
				if ( workers[i]!=null && !workers[i].isAlive() && workers[i].getStatus()==SGClosePowerThread.RUNNING ) {
					System.err.println("Uncaught exception in worker thread number "+i);
					StackTraceElement[] stackTrace = workers[i].getStackTrace();
					for ( int j = 0; j < stackTrace.length; j++ ) System.err.println(stackTrace[j]);
					workers[i]=null;
					if (reportNotNull) report.addLine("Worker "+i+" has died unexpectedly");
				} // end if ( workers[i]!=null && !workers[i].isAlive() && workers[i].getStatus()==SGClosePowerThread.RUNNING )
			} // end for 0 <= i < numWorkers
			
			boolean allDone = true;
			for ( int i = 0; i < numWorkers; i++ ) allDone = allDone && workersFinished[i];
			if (allDone) break;
			
			// Calculate the timing of it all
			if (reportNotNull) {
				report.setSize(ans.size());
				if ( chunksProcessedThisPass>0 ) {
					report.setTimeLeft(msToString((totalChunks-chunksProcessedThisPass)*(System.currentTimeMillis()-passStartTime)/chunksProcessedThisPass));
				} else {
					report.setTimeLeft("Unknown");
				} // end if-else ( chunksProcessedThisPass>0 )
				long futureElements=-1*totalElements;
				long size = ans.size();
				for ( int r = 0; r < numOfOps; r++ ) {
					long addendum = 1;
					for ( int i = 0; i < arities[r]; i++ ) addendum*=size;
					futureElements+=addendum;
				} // end for 0 <= r < numOfOps
				if ( chunksProcessedThisPass>0 ) {
					report.setTimeNext(msToString(futureElements*totalChunks*(System.currentTimeMillis()-passStartTime)/(totalElements*chunksProcessedThisPass)));
				} else {
					report.setTimeNext("Unknown");
				} // end if-else ( chunksProcessedThisPass>0 )
			} // end if (reportNotNull)						
		} // end while (true)
		killThreads(workers,feederThread);
		return true;
	} // end onePassParallel()

	public boolean onePassEqualWorkload() {
		final boolean imgAlgNull = imgOps==null;
		final boolean eltToFindNotNull = eltToFind!=null;
		final boolean eltsToFindNotNull = eltsToFind!=null;
		final boolean operationsNotNull = operations!=null;
		final boolean termMapNotNull = termMap!=null;

		final int numWorkers = numThreads==0?Runtime.getRuntime().availableProcessors():numThreads;
		final Set<IntArray> suTemp = Collections.newSetFromMap(new ConcurrentHashMap<IntArray,Boolean>());
		suTemp.addAll(su);
		final ReadWriteLock ansLock = new ReentrantReadWriteLock();
		final ReadWriteLock rawListLock = new ReentrantReadWriteLock();
		final Map<IntArray,Term> termMapTemp = termMap==null?null:new ConcurrentHashMap<IntArray,Term>(termMap);
		final Map<Operation,Term> termMapForOperationsTemp = termMapForOperations==null?null:new ConcurrentHashMap<Operation,Term>(termMapForOperations);
		final ReadWriteLock operationsFoundLock = new ReentrantReadWriteLock();
		final Map<IntArray,Integer> indicesMapOfFoundEltsTemp = indicesMapOfFoundElts==null?null:new ConcurrentHashMap<IntArray,Integer>(indicesMapOfFoundElts);
		final ReadWriteLock specialEltsFoundLock = new ReentrantReadWriteLock();
		final Map<IntArray,Integer> homomorphismTemp = homomorphism==null?null:new ConcurrentHashMap<IntArray,Integer>(homomorphism);
		final List<ReentrantLock> opLocks = new ArrayList<ReentrantLock>();
		for ( int i = 0; i < ops.size(); i++ ) opLocks.add(new ReentrantLock());
		
		class SGCloseTask implements Runnable {
			private int index;
			public boolean finished = false;
			
			public SGCloseTask( int newIndex ) {
				index = newIndex;
			} // end constructor(int)
			
			@Override
			public void run() {
				for ( int i = 0; i < ops.size(); i++ ) {
					Operation f = ops.get(i);
					ReentrantLock opLock = opLocks.get(i);
					int arity = f.arity();
					if (arity==0) continue;
					int[] argIndices = new int[arity];
					for ( int j = 0; j < arity-1; j++ ) argIndices[j]=0;
					argIndices[arity-1]=index-numWorkers;
					ArrayIncrementor inc = SequenceGenerator.blockSequenceIncrementor(argIndices, currentMark-1, closedMark, numWorkers);
					final int[][] arg = new int[arity][];
					while (inc.increment()) {
						if (Thread.currentThread().isInterrupted()) return;
						rawListLock.readLock().lock();
						for ( int j = 0; j < arity; j++ ) arg[j] = rawList.get(argIndices[j]);
						rawListLock.readLock().unlock();
						opLock.lock();
						int[] vRaw = f.valueAt(arg);
						opLock.unlock();
						IntArray v = new IntArray(vRaw);
						if (suTemp.add(v)) {
							ansLock.writeLock().lock();
							ans.add(v);
							ansLock.writeLock().unlock();
							rawListLock.writeLock().lock();
							rawList.add(vRaw);
							rawListLock.writeLock().unlock();
							if ( termMapNotNull ) {
								List<Term> children = new ArrayList<Term>(arity);
								ansLock.readLock().lock();
								for ( int j = 0; j < arity; j++ ) children.add(termMapTemp.get(ans.get(argIndices[j])));
								ansLock.readLock().unlock();
								termMapTemp.put(v, new NonVariableTerm(f.symbol(), children));
								if (operationsNotNull) {
									Term term = termMapTemp.get(v);
									List<Variable> vars = new ArrayList<Variable>(generators.size());
									for ( IntArray ia : generators ) vars.add((Variable)termMapTemp.get(ia));
									Operation termOp = term.interpretation(rootAlgebra, vars, true);
									for ( Operation op : operations ) {
										if ( termMapForOperationsTemp.containsKey(op) && Operations.equalValues(termOp, op) ) {
											termMapForOperationsTemp.put(op, term);
											operationsFoundLock.writeLock().lock();
											operationsFound++;
											operationsFoundLock.writeLock().unlock();
											operationsFoundLock.readLock().lock();
											if ( operationsFound==operations.size() ) {
												operationsFoundLock.readLock().unlock();
												completed=true;
												finished=true;
												return;
											} else {
												operationsFoundLock.readLock().unlock();
											} // end if-else ( operationsFound==operations.size() )											
										} // end if ( termMapForOperationsTemp.containsKey(op) && Operations.equalValues(termOp, op) )
									} // end for ( Operation op : operations )
								} // end if (operationsNotNull)								
							} // end if (termMapNotNull)
							if (eltToFindNotNull && v.equals(eltToFind)) {
								completed=true;
								finished=true;
								return;
							} // end if (eltToFindNotNull && v.equals(eltToFind))
							if ( eltsToFindNotNull && MINUS_ONE.equals(indicesMapOfFoundEltsTemp.get(v)) ) {
								ansLock.readLock().lock();
								final int index = ans.size()-1;
								ansLock.readLock().unlock();
								indicesMapOfFoundEltsTemp.put(v, index);
								specialEltsFoundLock.writeLock().lock();
								specialEltsFound++;
								specialEltsFoundLock.writeLock().unlock();
								specialEltsFoundLock.readLock().lock();
								if ( specialEltsFound==eltsToFind.size() ) {
									specialEltsFoundLock.readLock().unlock();
									allEltsFound=true;
									completed=true;
									finished=true;
									return;
								} else {
									specialEltsFoundLock.readLock().unlock();
								} // end if-else ( specialEltsFound==eltsToFind.size() )
							} // end if ( eltsToFindNotNull && MINUS_ONE.equals(indicesMapOfFoundElts.get(v)) )
							if (imgAlgNull) {
								ansLock.readLock().lock();
								if ( algebra.cardinality()>0 && ans.size()==algebra.cardinality() ) {
									ansLock.readLock().unlock();
									completed=true;
									finished=true;
									return;
								} else {
									ansLock.readLock().unlock();
								} // end if ( algebra.cardinality()>0 && ans.size()==algebra.cardinality() )
							} else {
								final int[] args = new int[arity];
								ansLock.readLock().lock();
								for ( int t = 0; t < arity; t++ ) args[t]=homomorphismTemp.get(ans.get(argIndices[t]));
								ansLock.readLock().unlock();
								homomorphismTemp.put(v, imgOps[i].intValueAt(args));
							} // end if-else (imgAlgNull)
						} else {
							if ( imgOps!=null ) {
								final int[] args=new int[arity];
								ansLock.readLock().lock();
								for ( int t = 0; t < arity; t++ ) args[t]=homomorphismTemp.get(ans.get(argIndices[t]));
								ansLock.readLock().unlock();
								if ( homomorphismTemp.get(v).intValue() != imgOps[i].intValueAt(args) ) {
									List<Term> children = new ArrayList<Term>(arity);
									for ( int r = 0; r < arity; r++ ) children.add(termMapTemp.get(ans.get(argIndices[r])));
									failingEquation = new Equation( termMapTemp.get(v), new NonVariableTerm(imgOps[i].symbol(),children) );
									finished=true;
									completed=true;
									return;
								} // end if ( homomorphism.get(v).intValue() != imgOps.get(i).intValueAt(args) )
							} // end if ( imgOps!=null )
							
						} // end if-else (suTemp.add(v))
						
					} // end while (inc.increment())
				} // end for ( Operation f : ops )	
				finished=true;
			} // end run()
		} // end class SGCloseTask

		SGCloseTask[] work = new SGCloseTask[numWorkers];
		Thread[] workers = new Thread[numWorkers];
		for ( int i = 0; i < numWorkers; i++ ) {
			work[i]=new SGCloseTask(i);
			workers[i]=new Thread(work[i]);
		}
		for ( int i = 1; i < numWorkers; i++ ) workers[i].start();
		work[0].run();
		for ( int i = 0; i < numWorkers; i++ ) {
			if (!work[i].finished) {
				for ( int j = i+1; j < numWorkers; j++ ) if (workers[j].isAlive()) workers[j].interrupt();
				break;
			} // end if (!work[i].finished)
			if (i<numWorkers-1 && workers[i+1].isAlive()) try {
				workers[i+1].join();
			} catch ( InterruptedException e ) {				
			} // end try-catch InterruptedException
		} // end for 0 <= i < numWorkers
		
		su.addAll(suTemp);
		if (termMap!=null) termMap.putAll(termMapTemp);
		if (termMapForOperations!=null) termMapForOperations.putAll(termMapForOperationsTemp);
		if (indicesMapOfFoundElts!=null) indicesMapOfFoundElts.putAll(indicesMapOfFoundEltsTemp);
		if (homomorphism!=null) homomorphism.putAll(homomorphismTemp);
		
		if ( completed ) return false;
		boolean notDone = true;
		for ( int i = 0; i < numWorkers; i++ ) if (!work[i].finished) notDone=false;
		return notDone;
	} // end onePassEqualWorkload()
	
	private void initializeClosurePower() {
		if ( report!=null ) report.addStartLine("subpower closing...");
		BigProductAlgebra bpa = (BigProductAlgebra)algebra;
		algSize = bpa.factors().get(0).cardinality();
		ops = bpa.factors().get(0).operations();
		numOfOps = ops.size();
		opTables = new int[numOfOps][];
		symbols = new OperationSymbol[numOfOps];
		imgOps = (homomorphism!=null && imageAlgebra!=null && termMap!=null)?new Operation[numOfOps]:null;
		if ( imgOps!=null ) {
			imgOpTables = new int[numOfOps][];
			imageAlgebra.makeOperationTables();
			imgAlgSize = imageAlgebra.cardinality();
		} // end if ( imgOps!=null )
		arities = new int[numOfOps];
		for ( int i = 0; i < numOfOps; i++ ) {
			Operation op = ops.get(i);
			if ( op instanceof OperationWithDefaultValue ) {
				opTables[i]=((OperationWithDefaultValue)op).getTotalTable();
			} else {
				opTables[i]=op.getTable();
			} // end if-else ( op instanceof OperationWithDefaultValue )
			arities[i]=op.arity();
			symbols[i]=op.symbol();
			if (imgOps!=null) {
				imgOps[i]=imageAlgebra.getOperation(symbols[i]);
				Operation op2 = imageAlgebra.getOperation(symbols[i]);
				if ( op2 instanceof OperationWithDefaultValue ) {
					opTables[i] = ((OperationWithDefaultValue)op2).getTotalTable();
				} else {
					opTables[i]=op2.getTable();
				} // end if-else ( op2 instanceof OperationWithDefaultValue )
			} // end if (imgOps!=null)
		} // end for 0 <= i < numOfOps
		if ( operations!=null ) termMapForOperations = new HashMap<Operation,Term>();
		operationsFound=0;
		power=bpa.getNumberOfFactors();
		if ( ans==null || ans.size()==0 ) ans=new ArrayList<IntArray>(generators);
		rawList = new ArrayList<int[]>();
		for ( IntArray arr : ans ) rawList.add(arr.getArray());
		su = new HashSet<IntArray>(ans);
		for ( Operation op : bpa.operations() ) {
			if ( op.arity()==0 ) {
				IntArray ia = (IntArray)op.valueAt(new ArrayList<IntArray>());
				if ( su.add(ia) ) {
					ans.add(ia);
					rawList.add(ia.getArray());
					if (termMap!=null) termMap.put(ia, NonVariableTerm.makeConstantTerm(op.symbol()));
				} // end if ( su.add(ia) )
			} // end if ( op.arity()==0 )
		} // end for ( Operation op : ops )
/*		final List<IntArray> constants = algebra.getConstants();
		for ( IntArray arr : constants ) {
			if (su.add(arr)) {
				ans.add(arr);
				rawList.add(arr.getArray());
				if (termMap!=null) termMap.put(arr, NonVariableTerm.makeConstantTerm(algebra.constantToSymbol.get(arr)));
			} // end if (su.add(arr))
		} // end for ( IntArray arr : constants ) /**/
		currentMark = ans.size();
		pass=0;
		timing=(report!=null)?new CloserTiming(algebra,report):null;		
	} // end initializeClosurePower()
	
	public List<IntArray> sgClosePower() {
		if (pass==0) initializeClosurePower();
		
		while (closedMark<currentMark) {
			if (report!=null) {
				timing.updatePass(ans.size());
				report.setPass(pass);
				report.setPassSize(ans.size());
				if (!suppressOutput) report.addLine("pass: "+pass+", size: "+ans.size());
			} // end if (report!=null)
			pass++;
			boolean result = false;
			switch (currentPassType()) {
				case SERIAL: result = onePassPowerSerial(); break;
				case PARALLEL: result = onePassPowerParallel(); break;
				case EQUAL_WORKLOAD: result = onePassPowerEqualWorkload(); break;
			} // end switch (currentPassType())
			if (!result) return completed?ans:null;
			closedMark=currentMark;
			currentMark=ans.size();
			if (imageAlgebra==null && algebra.cardinality()>0 && currentMark>=algebra.cardinality() ) { 
				completed=true; 
				break; 
			} // end if (imageAlgebra==null && algebra.cardinality()>0 && currentMark>=algebra.cardinality() )
			if (stopEachPass) break;
		} // end while (closedMark<currentMark)
		if ((currentMark>=closedMark||completed) && report!=null) {
			report.setSize(ans.size());
			report.addEndingLine("done closing, size = "+ans.size());
		} // end if ((currentMark>=closedMark||completed) && report!=null)
		if ( closedMark>=currentMark ) completed = true;
		return ans;
	} // end sgClosePower()
	
	public boolean onePassPowerSerial() {
		final boolean reportNotNull = report!=null;
		final boolean imgAlgNull = imgOps==null;
		final boolean eltToFindNotNull = eltToFind!=null;
		final boolean eltsToFindNotNull = eltsToFind!=null;
		final boolean operationsNotNull = operations!=null;
		final boolean blocksNotNull = blocks!=null;
		final boolean valuesNotNull = values!=null;
		
		for ( int i = 0; i < numOfOps; i++ ) {
			final int arity = arities[i];
			if (arity==0) continue;
			int[] opTable = opTables[i];
			final int[] argIndices = new int[arity];
			for ( int r = 0; r < arity-1; r++ ) argIndices[r]=0;
			argIndices[arity-1]=closedMark;
			ArrayIncrementor inc = SequenceGenerator.sequenceIncrementor(argIndices, currentMark-1, closedMark);
			
			while (true) {
				if (Thread.currentThread().isInterrupted()) {
					if (reportNotNull) {
						report.setSize(ans.size());
						report.addEndingLine("cancelled...");
					}
					return false;
				} // end if (Thread.currentThread().isInterrupted())
				
				final int[] vRaw = new int[power];
				if (opTable!=null) {
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
					final Operation f = ops.get(i);
					for ( int j = 0; j < power; j++ ) {
						final int[] arg = new int[f.arity()];
						for ( int r = 0; r < arity; r++ ) arg[r]=rawList.get(argIndices[r])[j];
						vRaw[j]=f.intValueAt(arg);
					} // end for 0 <= j < power
				} // end if-else (opTable!=null)
				IntArray v = new IntArray(vRaw);
				if (reportNotNull) timing.incrementApps();
				if (su.add(v)) {
					ans.add(v);
					rawList.add(vRaw);
					if (reportNotNull) {
						timing.incrementNextPassSize();
						report.setSize(ans.size());
					} // end if (reportNotNull)
					if (Thread.currentThread().isInterrupted()) return false;
					if (termMap!=null) {
						List<Term> children = new ArrayList<Term>(arity);
						for ( int r = 0; r < arity; r++ ) children.add(termMap.get(ans.get(argIndices[r])));
						termMap.put(v, new NonVariableTerm(symbols[i],children));
						if (operationsNotNull) {
							Term term = termMap.get(v);
							List<Variable> vars = new ArrayList<Variable>(generators.size());
							for ( IntArray ia : generators ) vars.add((Variable)termMap.get(ia));
							Operation termOp = term.interpretation(rootAlgebra, vars, true);
							for ( Operation op : operations ) {
								if ( Operations.equalValues(termOp, op) ) {
									termMapForOperations.put(op, term);
									operationsFound++;
									if ( operationsFound==operations.size() ) {
										completed=true;
										return false;
									} // end if ( operationsFound==operations.size() )
								} // end if ( Operations.equalValues(termOp, op) )
							} // end for ( Operation op : operations )
						} // end if (operationsNotNull)
					} // end if (termMap!=null)
					if ( eltToFindNotNull && v.equals(eltToFind) ) {
						if (reportNotNull) {
							report.setSize(ans.size());
							report.addEndingLine("closing done, found "+eltToFind+", at "+ans.size());
						} // end if (reportNotNull)
						completed=true;
						return false;
					} // end if ( eltToFindNotNull && v.equals(eltToFind) )
					if ( eltsToFindNotNull && MINUS_ONE.equals(indicesMapOfFoundElts.get(v)) ) {
						final int index = ans.size()-1;
						indicesMapOfFoundElts.put(v, index);
						specialEltsFound++;
						if (reportNotNull) report.addLine("found "+v+", at "+index);
						if (specialEltsFound==eltsToFind.size()) {
							if (reportNotNull) report.addEndingLine("closing done, found all "+specialEltsFound+" elems");
							allEltsFound=true;
							completed=true;
							return false;
						} // end if (specialEltsFound==eltsToFind.size())
					} // end if ( eltsToFindNotNull && MINUS_ONE.equals(indicesMapOfFoundElts.get(v)) )
					if (blocksNotNull) {
						boolean found = false;
						if (valuesNotNull) {
							if (v.satisfiesConstraint(blocks, values)) found=true;
						} else {
							if (v.satisfiesConstraint(blocks)) found=true;
						} // end if-else (valuesNotNull)
						if (found) {
							eltToFind=v;
							if (reportNotNull) {
								report.setSize(ans.size());
								report.addEndingLine("closing done, found "+eltToFind+", at "+ans.size());
							} // end if (reportNotNull)
							completed=true;
							return false;
						} // end if (found)
					} // end if (blocksNotNull)
					
					if (imgOps==null) {
						final int size = ans.size();
						if ( imgAlgNull && algebra.cardinality()>0 && size==algebra.cardinality() ) {
							if (reportNotNull) {
								report.setSize(ans.size());
								report.addEndingLine("found all "+size+" elements");
							} // end if (reportNotNull)
							completed=true;
							return false;
						} // end if (imgAlgNull && algebra.cardinality()>0 && size==algebra.cardinality() )
					} else {
						final int[] args = new int[arity];
						for ( int t = 0; t < arity; t++ ) args[t]=homomorphism.get(ans.get(argIndices[t]));
						homomorphism.put(v, imgOps[i].intValueAt(args));
					} // end if-else (imgOps==null)
					if (Thread.currentThread().isInterrupted()) {
						if (reportNotNull) {
							report.setSize(ans.size());
							report.addEndingLine("cancelled...");
						} // end if (reportNotNull)
						return false;
					} // end if (Thread.currentThread().isInterrupted())					
				} else {
					if (!imgAlgNull) {
						final int[] args = new int[arity];
						for ( int t = 0; t < arity; t++ ) args[t] = homomorphism.get(ans.get(argIndices[t]));
						if ( homomorphism.get(v).intValue() != imgOps[i].intValueAt(args) ) {
							List<Term> children = new ArrayList<Term>(arity);
							for ( int r = 0; r < arity; r++ ) children.add(termMap.get(argIndices[r]));
							failingEquation = new Equation(termMap.get(v), new NonVariableTerm(symbols[i],children));
							if (reportNotNull) {
								report.setSize(ans.size());
								report.addEndingLine("failing equation:\n"+failingEquation);
							} // end if (reportNotNull)
							completed=true;
							return false;
						} // end if ( homomorphism.get(v).intValue() != imgOps[i].intValueAt(args) )
					} // end if (imgAlgNull)
				} // end if-else (su.add(v))
				if (!inc.increment()) break;
			} // end while (true)
		} // end for 0 <= i < numOfOps
		return true;
	} // end onePassPowerSerial()
	
	/**
	 * Performs one closure pass in parallel on a power algebra.
	 * @return Whether or not to continue closing
	 */
	public boolean onePassPowerParallel() {
		final long passStartTime = System.currentTimeMillis();
		final int numWorkers = Math.max((numThreads==0?Runtime.getRuntime().availableProcessors():numThreads)-(splitFeederThread?2:1),1);
		final boolean reportNotNull = report!=null;
		final boolean eltToFindNotNull = eltToFind!=null;
		final boolean eltsToFindNotNull = eltsToFind!=null;
		final boolean operationsNotNull = operations!=null;
		final boolean blocksNotNull = blocks!=null;
		final boolean valuesNotNull = values!=null;
		int unusedPasses = 0;
		final LinkedBlockingQueue<SGClosePowerThread.SGClosePowerChunk> feeder = new LinkedBlockingQueue<SGClosePowerThread.SGClosePowerChunk>(FEEDER_CAPACITY);
		final LinkedBlockingQueue<SGClosePowerThread.SGClosePowerResult> collector = new LinkedBlockingQueue<SGClosePowerThread.SGClosePowerResult>();
		SGClosePowerThread[] workers = new SGClosePowerThread[numWorkers];
		boolean[] workersFinished = new boolean[numWorkers];
		HashMap<IntArray,Term> prevTermMap = new HashMap<IntArray,Term>();
		if (termMap!=null) prevTermMap.putAll(termMap);
		List<int[]> prevRawList = new ArrayList<int[]>(rawList);
		HashMap<IntArray,Integer> prevHomomorphism = null;
		if ( imgOps!=null ) {
			prevHomomorphism = new HashMap<IntArray,Integer>();
			prevHomomorphism.putAll(homomorphism);
		} // end if ( imgOps!=null )
		for ( int i = 0; i < numWorkers; i++ ) {
			workers[i]=new SGClosePowerThread(feeder,power,opTables,algSize,arities,argumentsPerChunk,closedMark,currentMark,prevRawList,ops,prevTermMap,symbols,collector,i,imgOpTables,prevHomomorphism,imgAlgSize);
			workers[i].setPriority(THREAD_PRIORITY);
			workersFinished[i]=false;
			workers[i].start();
		} // end for 0 <= i < numWorkers
		SGClosePowerThread.SGClosePowerResult partResult = null;
		long chunksProcessedThisPass=0;
		long totalChunks = 0;
		for ( int i = 0; i < numOfOps; i++ ) {
			int addendum = 1;
			for ( int j = 0; j < arities[i]-argumentsPerChunk; j++ ) addendum *= currentMark;
			totalChunks+=addendum;
		} // end for 0 <= i < numOfOps
		long totalElements = 0;
		for ( int i = 0; i < numOfOps; i++ ) {
			int addendum = 1;
			for ( int j = 0; j < arities[i]; j++ ) addendum *= currentMark;
			totalElements+=addendum;
		} // end for 0 <= i < numOfOps		
		SGFeederRunner feederRunner = new SGFeederRunner(feeder,numWorkers);
		Thread feederThread = null;
		if ( splitFeederThread ) {
			feederThread = new Thread(feederRunner);
			feederThread.start();
		} // end if ( splitFeederThread )
		
		while (true) {
			// Check for task cancellation
			if (Thread.currentThread().isInterrupted()) {
				killThreads(workers,feederThread);
				if (reportNotNull) {
					report.setSize(ans.size());
					report.addEndingLine("cancelled...");
				} // end if (reportNotNull)
				return false;
			} // end if (Thread.currentThread().isInterrupted())
			
			// Feed the queue if necessary
			if (!splitFeederThread) {
				feederRunner.fillQueue();
				if (!feederRunner.hasMore() && feeder.remainingCapacity()>=numWorkers) for ( int i = 0; i < numWorkers; i++ ) feeder.offer(SGClosePowerThread.STOP_COMMAND);
			} // end if (!splitFeederThread)
			
			// Counting sheep
			if ( collector.size()==0 ) {
				unusedPasses++;
			} else {
				unusedPasses=0;
			} // end if-else ( collector.size()==0 )
			if ( unusedPasses>=MAX_UNUSED_PASSES ) {
				try {
					Thread.sleep(SGClosePowerThread.SLEEP_TIME);
				} catch ( InterruptedException e ) {}
				unusedPasses=0;
			} // end if ( unusedPasses>=MAX_UNUSED_PASSES )
			
			 // Collect and evaluate partial answers 
			for ( int q = 0; q < PROCESS_PER_LOOP; q++ ) {
				if (collector.size()==0) break;
				partResult = collector.poll();
				if ( partResult!=null && partResult.completed>=0 ) {
					workersFinished[partResult.completed]=true;
				} else if ( partResult!=null ){
					chunksProcessedThisPass++;
					if ( partResult.failingEquation!=null && homomorphism!=null ) {
						failingEquation = partResult.failingEquation;
						if (reportNotNull) {
							report.setSize(ans.size());
							report.addEndingLine("failing equation:\n"+failingEquation);
						} // end if (reportNotNull)
						completed=true;
						killThreads(workers,feederThread);
						return false;
					} // end if ( partResult.failingEquation!=null && homomorphism!=null )
					List<IntArray> partAns = new ArrayList<IntArray>(partResult.termMap.keySet());
					for ( IntArray v : partAns ) {
						if (su.add(v)) {
							ans.add(v);
							rawList.add(v.getArray());
							if (termMap!=null) {
								termMap.put(v, partResult.termMap.get(v));
								if (operationsNotNull) {
									Term term = partResult.termMap.get(v);
									List<Variable> vars = new ArrayList<Variable>(generators.size());
									for ( IntArray ia : generators ) vars.add((Variable)termMap.get(ia));
									Operation termOp = term.interpretation(rootAlgebra, vars, true);
									for ( Operation op : operations ) {
										if (Operations.equalValues(termOp, op)) {
											termMapForOperations.put(op, term);
											operationsFound++;
											if (operationsFound==operations.size()) {
												completed=true;
												killThreads(workers,feederThread);
												return false;
											} // end if (operationsFound==operations.size())
										} // end if (Operations.equalValues(termOp, op))
									} // end for ( Operation op : operations )
								} // end if (operationsNotNull)
							} // end if (termMap!=null)
							if ( eltToFindNotNull && v.equals(eltToFind) ) {
								if (reportNotNull) {
									report.setSize(ans.size());
									report.addLine("Closing done, found "+v+", at "+ans.size());
								} // end if (reportNotNull)
								completed=true;
								killThreads(workers,feederThread);
								return false;
							} // end if ( eltToFindNotNull && v.equals(eltToFind) )
							if ( eltsToFindNotNull && MINUS_ONE.equals(indicesMapOfFoundElts.get(v)) ) {
								final int index = ans.size()-1;
								indicesMapOfFoundElts.put(v, index);
								specialEltsFound++;
								if (reportNotNull) report.addLine("Found "+v+", at "+index);
								if ( specialEltsFound==eltsToFind.size() ) {
									if (reportNotNull) report.addEndingLine("Closing done, found all "+specialEltsFound+" elements");
									allEltsFound=true;
									completed=true;
									killThreads(workers,feederThread);
									return false;
								} // end if ( specialEltsFound==eltsToFind.size() )
							} // end if ( eltsToFindNotNull && MINUS_ONE.equals(indicesMapOfFoundElts.get(v)) )
							if (blocksNotNull) {
								boolean found=false;
								if (valuesNotNull) {
									if (v.satisfiesConstraint(blocks, values)) found=true;
								} else {
									if (v.satisfiesConstraint(blocks)) found=true;
								} // end if-else (valuesNotNull)
								if (found) {
									eltToFind=v;
									if (reportNotNull) {
										report.setSize(ans.size());
										report.addEndingLine("Closing done, found "+v+", at "+ans.size());
									} // end if (reportNotNull)
									completed=true;
									killThreads(workers,feederThread);
									return false;
								} // end if (found)
							} // end if (blocksNotNull)
							if ( imageAlgebra==null ) {
								final int size = ans.size();
								if ( algebra.cardinality()>0 && size==algebra.cardinality() ) {
									if (reportNotNull) {
										report.setSize(size);
										report.addEndingLine("Found all "+size+" elements");
									} // end if (reportNotNull)
									completed=true;
									killThreads(workers,feederThread);
									return false;
								} // end if ( algebra.cardinality>0 && size==algebra.cardinality() )
							} else {
								homomorphism.put(v, partResult.homomorphism.get(v));
							} // end if-else ( imageAlgebra==null )
						} else {
							if ( imageAlgebra!=null ) {
								if ( homomorphism.get(v).intValue()!=partResult.homomorphism.get(v).intValue() ) {
									failingEquation = new Equation(termMap.get(v), partResult.termMap.get(v));
									if (reportNotNull) {
										report.setSize(ans.size());
										report.addEndingLine("failing equation:\n"+failingEquation);
									} // end if (reportNotNull)
									completed=true;
									killThreads(workers,feederThread);
									return false;
								} // end if ( homomorphism.get(v).intValue()!=partResult.homomorphism.get(v).intValue() )
							} // end if ( imageAlgebra!=null )
						} // end if-else (su.add(v))
					} // end for ( IntArray v : partAns )
				} // end else if ( partResult!=null )
			} // end for 0 <= q < PROCESS_PER_LOOP
			
			// Check for dead workers, print any stack traces to the error stream and notify the user
			for ( int i = 0; i < numWorkers; i++ ) {
				if ( workers[i]!=null && !workers[i].isAlive() && workers[i].getStatus()==SGClosePowerThread.RUNNING ) {
					System.err.println("Uncaught exception in worker thread number "+i);
					StackTraceElement[] stackTrace = workers[i].getStackTrace();
					for ( int j = 0; j < stackTrace.length; j++ ) System.err.println(stackTrace[j]);
					workers[i]=null;
					if (reportNotNull) report.addLine("Worker "+i+" has died unexpectedly");
				} // end if ( workers[i]!=null && !workers[i].isAlive() && workers[i].getStatus()==SGClosePowerThread.RUNNING )
			} // end for 0 <= i < numWorkers
			
			boolean allDone = true;
			for ( int i = 0; i < numWorkers; i++ ) allDone = allDone && workersFinished[i];
			if (allDone) break;
			
			// Calculate the timing of it all
			if (reportNotNull) {
				report.setSize(ans.size());
				if ( chunksProcessedThisPass>0 ) {
					report.setTimeLeft(msToString((totalChunks-chunksProcessedThisPass)*(System.currentTimeMillis()-passStartTime)/chunksProcessedThisPass));
				} else {
					report.setTimeLeft("Unknown");
				} // end if-else ( chunksProcessedThisPass>0 )
				long futureElements=-1*totalElements;
				long size = ans.size();
				for ( int r = 0; r < numOfOps; r++ ) {
					long addendum = 1;
					for ( int i = 0; i < arities[r]; i++ ) addendum*=size;
					futureElements+=addendum;
				} // end for 0 <= r < numOfOps
				if ( chunksProcessedThisPass>0 ) {
					report.setTimeNext(msToString(futureElements*totalChunks*(System.currentTimeMillis()-passStartTime)/(totalElements*chunksProcessedThisPass)));
				} else {
					report.setTimeNext("Unknown");
				} // end if-else ( chunksProcessedThisPass>0 )
			} // end if (reportNotNull)
		} // end while (true)
		killThreads(workers,feederThread);
		return true;
	} // end onePassPowerParallel()
	
	public boolean onePassPowerEqualWorkload() {
		final boolean imgAlgNull = imgOps==null;
		final boolean eltToFindNotNull = eltToFind!=null;
		final boolean eltsToFindNotNull = eltsToFind!=null;
		final boolean operationsNotNull = operations!=null;
		final boolean blocksNotNull = blocks!=null;
		final boolean valuesNotNull = values!=null;
		final boolean termMapNotNull = termMap!=null;
		
		final int numWorkers = numThreads==0?Runtime.getRuntime().availableProcessors():numThreads;
		final ReadWriteLock rawListLock = new ReentrantReadWriteLock();
		final Set<IntArray> suTemp = Collections.newSetFromMap(new ConcurrentHashMap<IntArray,Boolean>());
		suTemp.addAll(su);
		final ReadWriteLock ansLock = new ReentrantReadWriteLock();
		final Map<IntArray,Term> termMapTemp = termMap==null?null:new ConcurrentHashMap<IntArray,Term>(termMap);
		final Map<Operation,Term> termMapForOperationsTemp = termMapForOperations==null?null:new ConcurrentHashMap<Operation,Term>(termMapForOperations);
		final ReadWriteLock operationsFoundLock = new ReentrantReadWriteLock();
		final Map<IntArray,Integer> indicesMapOfFoundEltsTemp = indicesMapOfFoundElts==null?null:new ConcurrentHashMap<IntArray,Integer>(indicesMapOfFoundElts);
		final ReadWriteLock specialEltsFoundLock = new ReentrantReadWriteLock();
		final Map<IntArray,Integer> homomorphismTemp = homomorphism==null?null:new ConcurrentHashMap<IntArray,Integer>(homomorphism);
		
		class SGClosePowerTask implements Runnable {
			private int index;
			public boolean finished = false;
			
			public SGClosePowerTask(int newIndex) {
				index=newIndex;
			} // end constructor(int)
			
			public void run() {
				for ( int i = 0; i < numOfOps; i++ ) {
					final int arity=arities[i];
					if (arity==0) continue;
					int[] opTable = opTables[i];
					final int[] argIndices = new int[arity];
					for ( int j = 0; j < arity-1; j++ ) argIndices[j]=0;
					argIndices[arity-1]=index-numWorkers;
					ArrayIncrementor inc = SequenceGenerator.blockSequenceIncrementor(argIndices, currentMark-1, closedMark, numWorkers);
					
					while (inc.increment()) {
						if (Thread.currentThread().isInterrupted()) return;
						int[] vRaw = new int[power];
						if (opTable!=null) {
							for ( int j = 0; j < power; j++ ) {
								int factor=algSize;
								rawListLock.readLock().lock();
								int index = rawList.get(argIndices[0])[j];
								for ( int r = 1; r < arity; r++ ) {
									index+=factor*rawList.get(argIndices[r])[j];
									factor=factor*algSize;
								} // end for 1 <= r < arity 
								rawListLock.readLock().unlock();
								vRaw[j]=opTable[index];
							} // end for 0 <= j < power
						} else {
							Operation f = ops.get(i);
							for ( int j = 0; j < power; j++ ) {
								final int[] arg = new int[f.arity()];
								for ( int r = 0; r < arity; r++ ) arg[r]=rawList.get(argIndices[r])[j];
								vRaw[j]=f.intValueAt(arg);								
							} // end for 0 <= j < power
						} // end if-else (optable!=null)
						IntArray v = new IntArray(vRaw);
						if (suTemp.add(v)) {
							ansLock.writeLock().lock();
							ans.add(v);
							ansLock.writeLock().unlock();
							rawListLock.writeLock().lock();
							rawList.add(vRaw);
							rawListLock.writeLock().unlock();
							if (termMapNotNull) {
								List<Term> children = new ArrayList<Term>(arity);
								ansLock.readLock().lock();
								for ( int r = 0; r < arity; r++ ) children.add(termMapTemp.get(ans.get(argIndices[r])));
								ansLock.readLock().unlock();
								termMapTemp.put(v, new NonVariableTerm(symbols[i],children));
								if (operationsNotNull) {
									Term term = termMapTemp.get(v);
									List<Variable> vars = new ArrayList<Variable>(generators.size());
									for ( IntArray ia : generators ) vars.add((Variable)termMapTemp.get(ia));
									Operation termOp = term.interpretation(rootAlgebra, vars, true);
									for ( Operation op : operations ) {
										if ( Operations.equalValues(termOp, op) ) {
											termMapForOperationsTemp.put(op, term);
											operationsFoundLock.writeLock().lock();
											operationsFound++;
											operationsFoundLock.writeLock().unlock();
											operationsFoundLock.readLock().lock();
											if ( operationsFound==operations.size() ) {
												operationsFoundLock.readLock().unlock();
												completed=true;
												finished=true;
												return;
											} else {
												operationsFoundLock.readLock().unlock();
											} // end if-else ( operationsFound==operations.size() )
										} // end if ( Operations.equalValues(termOp, op) )
									} // end for ( Operation op : operations )
								} // end if (operationsNotNull)
							} // end if (termMapNotNull)
							if ( eltToFindNotNull && v.equals(eltToFind) ) {
								completed=true;
								finished=true;
								return;
							} // end if ( eltToFindNotNull && v.equals(eltToFind) )
							if ( eltsToFindNotNull && MINUS_ONE.equals(indicesMapOfFoundEltsTemp.get(v)) ) {
								final int index = ans.size()-1;
								indicesMapOfFoundEltsTemp.put(v, index);
								specialEltsFoundLock.writeLock().lock();
								specialEltsFound++;
								specialEltsFoundLock.writeLock().unlock();
								specialEltsFoundLock.readLock().unlock();
								if (specialEltsFound==eltsToFind.size()) {
									specialEltsFoundLock.readLock().unlock();
									allEltsFound=true;
									completed=true;
									finished=true;
									return;
								} else {
									specialEltsFoundLock.readLock().unlock();
								} // end if-else (specialEltsFound==eltsToFind.size())
							} // end if ( eltsToFindNotNull && MINUS_ONE.equals(indicesMapOfFoundElts.get(v)) )
							if (blocksNotNull) {
								boolean found = false;
								if (valuesNotNull) {
									if (v.satisfiesConstraint(blocks, values)) found=true;
								} else {
									if (v.satisfiesConstraint(blocks)) found=true;
								} // end if-else (valuesNotNull)
								if (found) {
									eltToFind=v;
									completed=true;
									finished=true;
									return;
								} // end if (found)
							} // end if (blocksNotNull)
							
							if (imgOps==null) {
								final int size = ans.size();
								if ( imgAlgNull && algebra.cardinality()>0 && size==algebra.cardinality() ) {
									completed=true;
									finished=true;
									return;
								} // end if (imgAlgNull && algebra.cardinality()>0 && size==algebra.cardinality() )
							} else {
								final int[] args = new int[arity];
								ansLock.readLock().lock();
								for ( int t = 0; t < arity; t++ ) args[t]=homomorphismTemp.get(ans.get(argIndices[t]));
								ansLock.readLock().unlock();
								homomorphismTemp.put(v, imgOps[i].intValueAt(args));
							} // end if-else (imgOps==null)
						} else {
							if (!imgAlgNull) {
								final int[] args = new int[arity];
								ansLock.readLock().lock();
								for ( int t = 0; t < arity; t++ ) args[t] = homomorphismTemp.get(ans.get(argIndices[t]));
								ansLock.readLock().unlock();
								if ( homomorphismTemp.get(v).intValue() != imgOps[i].intValueAt(args) ) {
									List<Term> children = new ArrayList<Term>(arity);
									for ( int r = 0; r < arity; r++ ) children.add(termMapTemp.get(argIndices[r]));
									failingEquation = new Equation(termMapTemp.get(v), new NonVariableTerm(symbols[i],children));
									completed=true;
									finished=true;
									return;
								} // end if ( homomorphism.get(v).intValue() != imgOps[i].intValueAt(args) )
							} // end if (imgAlgNull)
						} // end if-else (su.add(v))
						
					} // end while (int.increment())
				} // end for 0 <= i < numOfOps
				finished=true;
			} // end run()
			
		} // end class SGClosePowerTask
		
		SGClosePowerTask[] work = new SGClosePowerTask[numWorkers];
		Thread[] workers = new Thread[numWorkers];
		for ( int i = 0; i < numWorkers; i++ ) {
			work[i]=new SGClosePowerTask(i);
			workers[i]=new Thread(work[i]);
		}
		for ( int i = 1; i < numWorkers; i++ ) workers[i].start();
		workers[0].run();
		for ( int i = 0; i < numWorkers; i++ ) {
			if (!work[i].finished) {
				for ( int j = i+1; j < numWorkers; j++ ) if (workers[j].isAlive()) workers[j].interrupt();
				break;
			} // end if (!work[i].finished)
			if (i<numWorkers-1 && workers[i+1].isAlive()) try {
				workers[i+1].join();
			} catch ( InterruptedException e ) {				
			} // end try-catch InterruptedException
		} // end for 0 <= i < numWorkers
		
		su.addAll(suTemp);
		if (termMap!=null) termMap.putAll(termMapTemp);
		if (termMapForOperations!=null) termMapForOperations.putAll(termMapForOperationsTemp);
		if (indicesMapOfFoundElts!=null) indicesMapOfFoundElts.putAll(indicesMapOfFoundEltsTemp);
		if (homomorphism!=null) homomorphism.putAll(homomorphismTemp);
		
		if ( completed ) return false;
		boolean notDone = true;
		for ( int i = 0; i < numWorkers; i++ ) if (!work[i].finished) notDone=false;
		return notDone;
	} // end onePassPowerEqualWorkload()
	
	private void killThreads(Thread[] workers, Thread feeder) {
		if (feeder!=null && feeder.isAlive()) {
			try {
				feeder.interrupt();
			} catch ( SecurityException e ) {
				if (report!=null) report.addLine("Could not cancel feeder thread");
				System.err.println("Could not cancel feeder thread");
				e.printStackTrace();
			} // end try-catch SecurityException
		} // end if (feeder!=null && feeder.isAlive())
		for ( int i = 0; i < workers.length; i++ ) {
			if ( workers[i]!=null && workers[i].isAlive() ) {
				try {
					workers[i].interrupt();
				} catch ( SecurityException e ) {
					if (report!=null) report.addLine("Could not cancel worker number "+i);
					System.err.println("Could not cancel worker number "+i);
					e.printStackTrace();
				} // end try-catch SecurityException
			} // end if ( workers[i]!=null && workers[i].isAlive() )
		} // end for 0 <= i < workers.length
	} // end killThreads(Thread[], Thread)
	
	public static String msToString(double ms) {
		final long totSecs = Math.round(ms/1000);
		final long secs = totSecs%60;
		final long totMins = totSecs/60;
		final long mins = totMins%60;
		final long hrs = totMins/60;
		String secString = secs<10 ? "0"+Long.toString(secs) : Long.toString(secs);
		if ( hrs==0 ) {
			if ( mins==0 ) return secString;
			return Long.toString(mins) + ":" + secString;
		} // end if ( hrs==0 )
		String minString = mins<10 ? "0"+Long.toString(mins) : Long.toString(mins);
		return Long.toString(hrs) + ":" + minString + ":" + secString;
	} // end msToString(double)
	
	public boolean equalCalculationStage( Closer2 target ) {
		if (pass!=target.getPass()) return false;
		if (!(new HashSet<IntArray>(ans)).equals(new HashSet<IntArray>(target.getAnswer()))) return false;
		if ( (termMap==null && target.getTermMap()!=null) || (termMap!=null && target.getTermMap()==null) ) return false;
		if ( !(algebra instanceof SmallProductAlgebra) ) return false;
		if ( termMap!=null && target.getTermMap()!=null ) 
			for ( IntArray ia : ans ) {
				if (!Operations.equalValues(termMap.get(ia).interpretation((SmallProductAlgebra)algebra), target.getTermMap().get(ia).interpretation((SmallProductAlgebra)algebra))) return false;
			} // end for ( IntArray ia : ans )
		if ((homomorphism!=null && !homomorphism.equals(target.getHomomorphism()))||(homomorphism==null&&target.getHomomorphism()!=null)) return false;
		return true;
	} // end equalCalculationStage(Closer2)/**/

	/**
	 * This class fills the feeder <code>java.util.concurrent.BlockingQueue</code> in a separate Thread
	 * @author Jonah Horowitz
	 */
	private class SGFeederRunner implements Runnable {
		private int opIndex=-1;
		private int arity;
		private SequenceIterator intArrayGen;
		private SGClosePowerThread.SGClosePowerChunk tempChunk = null;
		private LinkedBlockingQueue<SGClosePowerThread.SGClosePowerChunk> feeder;
		private int numWorkers;
		
		public SGFeederRunner(LinkedBlockingQueue<SGClosePowerThread.SGClosePowerChunk> newFeeder, int newNumWorkers) {
			feeder = newFeeder;
			numWorkers = newNumWorkers;
			nextOp();
		} // end constructor()
		
		private void nextOp() {
			tempChunk=null;
			opIndex++;
			if (opIndex>=numOfOps) return;
			arity=arities[opIndex];
			while ( arity==0 && opIndex<numOfOps ) {
				opIndex++;
				if (opIndex<numOfOps) arity=arities[opIndex];
			} // end while ( arity==0 && opIndex<numOfOps )
			int[] tempSegment = new int[arity<=argumentsPerChunk?0:arity-argumentsPerChunk];
			for ( int i = 0; i < tempSegment.length; i++ ) tempSegment[i]=0;
			intArrayGen = new SequenceIterator(tempSegment,currentMark-1,0);
		} // end nextOp()
		
		public boolean hasMore() {
			return opIndex<numOfOps;
		} // end hasMore()
		
		public void fillQueue() {
			while ( opIndex < numOfOps && feeder.remainingCapacity()!=0 ) {
				if (tempChunk!=null && !feeder.offer(tempChunk)) return;
				if (!intArrayGen.hasNext()) nextOp();
				tempChunk=new SGClosePowerThread.SGClosePowerChunk(opIndex, intArrayGen.next());
			} // end while ( opIndex < numOfOps && feeder.remainingCapacity()!=0 )
		} // end fillQueue()
		
		@Override
		public void run() {
			while (hasMore()) {
				fillQueue();
				try {
					Thread.sleep(SGClosePowerThread.SLEEP_TIME);
				} catch ( InterruptedException e ) {}
			} // end while(hasMore())
			while (feeder.remainingCapacity()<numWorkers) {
				try {
					Thread.sleep(SGClosePowerThread.SLEEP_TIME);
				} catch ( InterruptedException e ) {}
			} // end while (feeder.remainingCapacity()<numWorkers)
			for ( int i = 0; i < numWorkers; i++ ) feeder.offer(SGClosePowerThread.STOP_COMMAND);
		} // end run()
	} // end class SGFeederRunner
} // end class Closer2
