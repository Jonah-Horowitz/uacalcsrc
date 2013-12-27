package org.uacalc.example;

import org.uacalc.alg.op.*;
import org.uacalc.alg.*;

import java.util.*;

import org.uacalc.util.Horner;
import org.uacalc.util.IntArray;
import org.uacalc.io.*;
import org.uacalc.ui.tm.CLIProgressReport;
import org.uacalc.terms.*;

import java.io.*;

public class Horowitz {
	public static String ALGEBRA_DIR = "resources\\algebras\\";
	
	private Vector<Thread> tasks = new Vector<Thread>();
	private Vector<String> taskTypes = new Vector<String>();
	private Vector<CLIProgressReport> reports = new Vector<CLIProgressReport>();
	private Map<String,Algebra> algs = new HashMap<String,Algebra>();
	private Map<String,String> algFiles = new HashMap<String,String>();
	
	public Horowitz() {		
	} // end constructor()
	
	/** Integer function which raises base to exp
	 * @param base The base of the exponential function
	 * @param exp The exponent of the exponential function
	 * @return base**exp
	 */
	public static int pow(int base, int exp) {
		int ans = 1;
		for ( int i = 0; i < exp; i++ ) {
			ans*=base;
		}
		return ans;
	}

	/** Creates a new (almost) Jonsson operation under the given constraints
	 * @param name The name of the new Jonsson operation
	 * @param universeSize The size of the universe
	 * @param prevJonssonOperation The preceding Jonsson operation in sequence, if null assume this is the first in sequence
	 * @param n The position of the Jonsson operation in sequence
	 * @param isLast Whether or not this is the last Jonsson operation in sequence
	 * @param exceptArgs The argument for which to make an exception
	 * @param excepti The index at which to make an exception
	 * @return An <org.uacalc.alg.op.Operation> in the specified (almost) Jonsson sequence
	 */
	public static Operation makeRandomAlmostJonssonOperation(String name, int universeSize, Operation prevJonssonOperation, int n, boolean isLast, int[] exceptArgs, int excepti) {
		return makeRandomAlmostJonssonOperation(name, universeSize, prevJonssonOperation, n, isLast, exceptArgs, excepti, new Random());
	}
	
	/** Tests to see if two <code>int[]</code>'s of length 3 are equal. Can compare <code>null</code> values (will always return false)
	 * @param a1 The first int[]
	 * @param a2 The second int[]
	 * @return Whether or not a1==a2
	 */
	private static boolean array3Equals(int[] a1, int[] a2) {
		if ( a1==null || a2==null ) {
			return false;
		}
		return a1[0]==a2[0] && a1[1]==a2[1] && a1[2]==a2[2];
	}
	
	/** Randomly chooses a different integer
	 * @param random A random number generator
	 * @param target The target to be avoided
	 * @param max The value to be fed into random's nextInt method
	 * @return A random int n with 0<= n < max and n!=target uniformly distributed  
	 */
	private static int pickDifferentInt(Random random, int target, int max) {
		if ( max==1 ) {
			return 0;
		}
		int ans=target;
		while ( ans==target ) {
			ans=random.nextInt(max);
		}
		return ans;
	}
	
	/** Creates a new Jonsson operation under the given constraints
	 * @param name The name of the new Jonsson operation
	 * @param universeSize The size of the universe
	 * @param prevJonssonOperation The preceding Jonsson operation in sequence, if null assume this is the first in sequence
	 * @param n The position of the Jonsson operation in sequence
	 * @param isLast Whether or not this is the last Jonsson operation in sequence
	 * @param exceptArgs The argument for which to make an exception
	 * @param excepti The index at which to make an exception
	 * @param random A random number generator
	 * @return An <org.uacalc.alg.op.Operation> in the specified Jonsson sequence
	 */
	public static Operation makeRandomAlmostJonssonOperation(String name, int universeSize, Operation prevJonssonOperation, int n, boolean isLast, int[] exceptArgs, int excepti, Random random) {
		final int arity = 3;
		int[] vals = new int[pow(universeSize,arity)];
		for ( int i = 0; i < vals.length; i++) {
			int[] args = Horner.hornerInv(i, universeSize, arity);
			if ( args[0]==args[1] && args[1]==args[2] ) {
				vals[i]=args[0];
			} else if ( args[0]==args[2] ) {
				if ( array3Equals(args,exceptArgs) && n==excepti ) {
					vals[i]=pickDifferentInt(random,args[0],universeSize);
				} else {
					vals[i] = args[0];
				}
			} else if ( args[0]==args[1] ) {
				if ( n%2==1 ) {
					if ( prevJonssonOperation==null ) {
						vals[i]=args[0];
					} else {
						vals[i]=prevJonssonOperation.intValueAt(i);
					}
					if ( array3Equals(args,exceptArgs) && n==excepti+1 ) {
						vals[i]=pickDifferentInt(random,vals[i],universeSize);
					}
				} else if ( isLast ) {
					if ( array3Equals(args,exceptArgs) && n==excepti ) {
						vals[i]=pickDifferentInt(random,args[2],universeSize);
					} else {
						vals[i]=args[2];
					}
				} else {
					vals[i]=random.nextInt(universeSize);
				}
			} else if ( args[1]==args[2] ) {
				if ( n%2==0 ) {
					if ( prevJonssonOperation==null ) {
						vals[i]=args[0];
					} else {
						vals[i]=prevJonssonOperation.intValueAt(i);
					}
					if ( array3Equals(args,exceptArgs) && n==excepti+1 ) {
						vals[i]=pickDifferentInt(random,vals[i],universeSize);
					}
				} else if ( isLast ) {
					if ( array3Equals(args,exceptArgs) && n==excepti ) {
						vals[i]=pickDifferentInt(random,args[2],universeSize);
					} else {
						vals[i]=args[2];
					}
				} else {
					vals[i]=random.nextInt(universeSize);
				}
			} else {
				vals[i]=random.nextInt(universeSize);
			}
		}
		return Operations.makeIntOperation(new OperationSymbol(name,arity), universeSize, vals);
	}
	
	/** Creates a name for the (almost) Jonsson operation specified
	 * @param i The position in the Jonsson sequence
	 * @param exceptArgs The arguments being excepted
	 * @param excepti The position of the arguments being excepted
	 * @return A String
	 */
	private static String makeAlmostJonssonName( int i, int[] exceptArgs, int excepti ) {
		return "d"+excepti+exceptArgs[0]+exceptArgs[1]+exceptArgs[2]+i;
	}
	
	/** Creates a sequence of (almost) Jonsson operations
	 * @param universeSize The size of the algebra's universe
	 * @param jonssonLevel The Jonsson level of the algebra to be created
	 * @return A <java.util.Vector<org.uacalc.alg.op.Operation>> consisting of n-ary (almost) Jonsson operations
	 */
	public static Vector<Operation> makeRandomAlmostJonssonSequence( int universeSize, int jonssonLevel, int[] exceptArgs, int excepti ) {
		Vector<Operation> ops = new Vector<Operation>();
		Operation prevOp = null;
		for ( int i = 1; i < jonssonLevel; i++ ) {
			prevOp = makeRandomAlmostJonssonOperation(makeAlmostJonssonName(i,exceptArgs,excepti),universeSize,prevOp,i,i==jonssonLevel-1, exceptArgs, excepti);
			ops.add(prevOp);
		}
		return ops;
	}
	
	/** Creates a <code>org.uacalc.alg.BasicAlgebra</code> with all sequences of random (almost) Jonsson operations
	 * @param name The name for the algebra
	 * @param universeSize The size of the universe
	 * @param jonssonLevel The Jonsson level for the algebra
	 * @return The algebra in question
	 */
	public static BasicAlgebra makeRandomAlmostJonssonAlgebra( String name, int universeSize, int jonssonLevel ) {
		Vector<Operation> ops = new Vector<Operation>();
		for ( int i = 0; i < jonssonLevel; i++ ) {
			for ( int x = 0; x < universeSize; x++ ) {
				for ( int y = 0; y < universeSize; y++ ) {
					if ( x==y ) continue;
					ops.addAll(makeRandomAlmostJonssonSequence(universeSize, jonssonLevel, new int[] {x,y,x}, i));
					if ( i%2==0 ) {
						ops.addAll(makeRandomAlmostJonssonSequence(universeSize, jonssonLevel, new int[] {x,x,y}, i));
					} else {
						ops.addAll(makeRandomAlmostJonssonSequence(universeSize, jonssonLevel, new int[] {x,y,y}, i));
					}
				}
			}
		}
		return new BasicAlgebra(name, universeSize, ops);
	}
	
	/** Creates a mutant version of an (almost) Jonsson algebra of the type created by makeAlmostJonssonAlgebra
	 * @param alg The base algebra which will generate the mutant
	 * @param jonssonLevel the Jonsson level of alg
	 * @param tackNumber a number to tack on the end of alg's name to generate the name of the new algebra
	 * @return A new <org.uacalc.alg.BasicAlgebra> which differs only slightly from alg
	 */
	public static BasicAlgebra mutateAlmostJonssonAlgebra( final BasicAlgebra alg, int jonssonLevel, int tackNumber ) {
		return mutateAlmostJonssonAlgebra( alg, jonssonLevel, tackNumber, new Random() );
	}
	
	/** Returns a copy of the given int array
	 * @param target An array of ints
	 * @return A copy of the given array of ints
	 */
	public static int[] copyIntArray( final int[] target ) {
		int[] ans = new int[target.length];
		for ( int i = 0; i < ans.length; i++ ) {
			ans[i]=target[i];
		}
		return ans;
	}
	
	/** Creates a mutant version of an (almost) Jonsson algebra of the kind created by makeAlmostJonssonAlgebra
	 * @param alg The base algebra which will generate the mutant
	 * @param jonssonLevel the Jonsson level of alg
	 * @param tackNumber a number to tack on the end of alg's name to generate the name of the new algebra
	 * @param random a random number generator
	 * @return A new <org.uacalc.alg.BasicAlgebra> which differs only slightly from alg
	 */
	public static BasicAlgebra mutateAlmostJonssonAlgebra( final BasicAlgebra alg, int jonssonLevel, int tackNumber, Random random ) {
		int universeSize = alg.cardinality();
		int x = -1;
		int y = -1;
		
		// Select which operation to alter
		while ( x==y ) {
			x=random.nextInt(universeSize);
			y=random.nextInt(universeSize);
		}
		int excepti = random.nextInt(jonssonLevel);
		int[] exceptArgs = new int[3];
		if ( random.nextBoolean() ) {
			if ( excepti%2==0 ) {
				exceptArgs = new int[] {x,x,y};
			} else {
				exceptArgs = new int[] {x,y,y};
			}
		} else {
			exceptArgs = new int[] {x,y,x};
		}
		int actuali = random.nextInt(jonssonLevel-1)+1;
		
		// Copy the operations from the old algebra, excepting those operations which may be altered
		Map<OperationSymbol,Operation> baseOps = new HashMap<OperationSymbol,Operation>();
		baseOps.putAll(alg.getOperationsMap());
		Operation targetOp = baseOps.remove(new OperationSymbol(makeAlmostJonssonName(actuali,exceptArgs,excepti),3));
		Operation preOp = null;
		if ( actuali>1 ) {
			preOp = baseOps.remove(new OperationSymbol(makeAlmostJonssonName(actuali-1,exceptArgs,excepti),3));
		}
		Operation postOp = null;
		if ( actuali<jonssonLevel-1 ) {
			postOp = baseOps.remove(new OperationSymbol(makeAlmostJonssonName(actuali+1,exceptArgs,excepti),3));
		}
		Vector<Operation> newOps = new Vector<Operation>(baseOps.values());
		int[] targetOpTable = copyIntArray(targetOp.getTable(true));
		int[] preOpTable = null;
		if ( preOp != null ) {
			preOpTable = copyIntArray(preOp.getTable(true));
		}
		int[] postOpTable = null;
		if ( postOp != null ) {
			postOpTable = copyIntArray(postOp.getTable(true));
		}
		
		// Pick out the value to be altered
		int actualHorner = 0;
		int[] actualArgs = Horner.hornerInv(actualHorner, universeSize, targetOp.arity());
		boolean hitException = false;
		boolean found = false; // Whether or not we've found an appropriate value to alter
		while ( !found ) {
			actualHorner = random.nextInt(targetOpTable.length);
			actualArgs = Horner.hornerInv(actualHorner, universeSize, targetOp.arity());
			hitException = array3Equals(actualArgs,exceptArgs);
			found=true;
			if ( actualArgs[0]==actualArgs[1] && actualArgs[1]==actualArgs[2] ) { // If we're messing with idempotence, start again
				found=false;
			} else if ( actualArgs[0]==actualArgs[2] ) { // If we fit the xyx pattern
				found=actuali==excepti && hitException; // Unless we've hit the exception, start again
			} else if ( actualArgs[0]==actualArgs[1] && actuali==1 ) { // If we're at the start and hit the xxy pattern
				found=excepti==0 && hitException; // Unless we've hit the exception, start again
			} else if ( actualArgs[0]==actualArgs[1] && actuali==jonssonLevel-1 && jonssonLevel%2==1 ) { // If we're at the end and hit the xxy pattern
				found=excepti==jonssonLevel-1 && hitException; // Unless we've hit the exception, start again
			} else if ( actualArgs[1]==actualArgs[2] && actuali==jonssonLevel-1 && jonssonLevel%2==0 ) { // If we're at the end and hit the xyy pattern
				found=excepti==jonssonLevel-1 && hitException; // Unless we've hit the exception, start again
			}
		}
		
		// Alter the chosen value randomly, altering the preceding or succeeding operation as well if necessary
		if ( actualArgs[0]==actualArgs[2] ) {
			int prevValue = targetOpTable[actualHorner];
			while ( targetOpTable[actualHorner]==prevValue && universeSize>2 ) {
				targetOpTable[actualHorner] = pickDifferentInt(random, actualArgs[0], universeSize);
			}
		} else {
			targetOpTable[actualHorner] = pickDifferentInt(random,targetOpTable[actualHorner],universeSize);
			if ( (actualArgs[0]==actualArgs[1]&&actuali%2==1) || (actualArgs[1]==actualArgs[2]&&actuali%2==0) ) {
				if ( actuali==excepti+1 && hitException ) {
					if ( preOpTable != null && preOpTable[actualHorner]==targetOpTable[actualHorner] ) {
						preOpTable[actualHorner]=pickDifferentInt(random, targetOpTable[actualHorner], universeSize);
					}
				} else {
					preOpTable[actualHorner]=targetOpTable[actualHorner];
				}
			} else if ( (actualArgs[0]==actualArgs[1]&&actuali%2==0) || (actualArgs[1]==actualArgs[2]&&actuali%2==1) ) {
				if ( actuali==excepti && hitException ) {
					if ( postOpTable != null && postOpTable[actualHorner]==targetOpTable[actualHorner] ) {
						postOpTable[actualHorner]=pickDifferentInt(random, targetOpTable[actualHorner], universeSize);
					}
				} else {
					postOpTable[actualHorner]=targetOpTable[actualHorner];
				}
			}
		}
		
		// Reconstruct the altered operations and return the new algebra
		newOps.addElement(Operations.makeIntOperation(targetOp.symbol(),universeSize,targetOpTable));
		if ( preOp != null ) {
			newOps.addElement(Operations.makeIntOperation(preOp.symbol(),universeSize,preOpTable));
		}
		if ( postOp != null ) {
			newOps.addElement(Operations.makeIntOperation(postOp.symbol(),universeSize,postOpTable));
		}
		return new BasicAlgebra(alg.getName()+"-"+tackNumber,universeSize,newOps);
	}
	
	/** Creates an (almost) Jonsson operation with default element 0, 1 when disagreement is required. 
	 * @param name The name of the new operation
	 * @param universeSize The size of the universe
	 * @param n The position in the (almost) Jonsson sequence
	 * @param isLast Whether or not this is the last operation in sequence
	 * @param exceptArgs The argument for which to make an exception
	 * @param excepti The index at which to make an exception
	 * @return An (almost) Jonsson operation in sequence
	 */
	public static Operation makeFlatAlmostJonssonOperation(String name, int universeSize, int n, boolean isLast, int[] exceptArgs, int excepti) {
		if ( universeSize<=1 ) {
			return null;
		}
		final int arity=3;
		int[] vals = new int[pow(universeSize,arity)];
		for ( int i = 0; i < vals.length; i++ ) {
			int[] args = Horner.hornerInv(i, universeSize, arity);
			boolean hitException = array3Equals(args,exceptArgs);
			if ( args[0]==args[1] && args[1]==args[2] ) {
				vals[i]=args[0];
			} else if ( args[0]==args[2] ) {
				if ( excepti==n && hitException ) {
					vals[i]= args[0]==0 ? 1 : 0;
				} else {
					vals[i]=args[0];
				}
			} else if ( args[0]==args[1] && n==1 ) {
				if ( excepti==0 && hitException ) {
					vals[i]= args[0]==0 ? 1 : 0;
				} else {
					vals[i]=args[0];
				}
			} else if ( args[1]==args[2] && isLast ) {
				if ( excepti==n && hitException ) {
					vals[i]= args[2]==0 ? 1 : 0;
				} else {
					vals[i]=args[2];
				}
			} else if ( n==excepti+1 && hitException ) {
				vals[i]=1;
			} else {
				vals[i]=0;
			}
		}
		return Operations.makeIntOperation(new OperationSymbol(name,arity), universeSize, vals);
	}

	/** Creates a sequence of (almost) Jonsson operations
	 * @param universeSize The size of the universe
	 * @param jonssonLevel The length of the (almost) Jonsson sequence
	 * @param exceptArgs The argument for which to make an exception
	 * @param excepti The position at which to make an exception
	 * @return
	 */
	public static Vector<Operation> makeFlatAlmostJonssonSequence( int universeSize, int jonssonLevel, int[] exceptArgs, int excepti ) {
		Vector<Operation> ops = new Vector<Operation>();
		for ( int i = 1; i < jonssonLevel; i++ ) {
			ops.add(makeFlatAlmostJonssonOperation(makeAlmostJonssonName(i,exceptArgs,excepti),universeSize,i,i==jonssonLevel-1,exceptArgs,excepti));
		}
		return ops;
	}

	/** Creates a <code>org.uacalc.alg.BasicAlgebra</code> with all sequences of flat (almost) Jonsson operations
	 * @param name The name for the new algebra
	 * @param universeSize The size of the universe
	 * @param jonssonLevel The Jonsson level of the new algebra
	 * @return The new algebra
	 */
	public static BasicAlgebra makeFlatAlmostJonssonAlgebra( String name, int universeSize, int jonssonLevel ) {
		Vector<Operation> ops = new Vector<Operation>();
		for ( int i = 0; i < jonssonLevel; i++ ) {
			for ( int x = 0; x < universeSize; x++ ) {
				for ( int y = 0; y < universeSize; y++ ) {
					if ( x==y ) continue;
					ops.addAll(makeFlatAlmostJonssonSequence(universeSize,jonssonLevel,new int[] {x,y,x}, i));
					if ( i%2==0 ) {
						ops.addAll(makeFlatAlmostJonssonSequence(universeSize, jonssonLevel, new int[] {x,x,y}, i));
					} else {
						ops.addAll(makeFlatAlmostJonssonSequence(universeSize, jonssonLevel, new int[] {x,y,y}, i));
					}
				}
			}
		}
		return new BasicAlgebra(name, universeSize, ops);
	}

	/**
	 * Checks (and prints) the status of task <code>i</code>
	 */
	private void checkOn(int i) {
		if ( taskTypes.get(i).equalsIgnoreCase("jonsson") ) {
			CLIProgressReport r=reports.get(i);
			System.out.println("Task is: "+(tasks.get(i).isAlive()?"Running":"Stopped"));
			System.out.println("Pass: "+r.getPass());
			System.out.println("Pass Size: "+r.getPassSize());
			System.out.println("Size: "+r.getSize());
			System.out.println("Time Left Pass: "+r.getTimeLeft());
			System.out.println("Time Left Next: "+r.getTimeNext());
		} else if ( "cancelafter".equalsIgnoreCase(taskTypes.get(i)) ) {
			System.out.println("Task is: "+(tasks.get(i).isAlive()?"Running":"Stopped"));
		} // end switch (taskTypes.get(i))
	} // end checkOn(int)
	
	public static boolean check3GeneratedSubalgebras(SmallAlgebra alg, int power) {
		SmallProductAlgebra bpa = new SmallProductAlgebra(alg, power);
		int algSize = alg.cardinality();
		int productSize = bpa.cardinality();
		for ( int i = 0; i < productSize-2; i++ ) {
			for ( int j = i+1; j < productSize-1; j++ ) {
				for ( int k = j+1; k < productSize; k++ ) {
					List<IntArray> gens = new ArrayList<IntArray>();
					gens.add(new IntArray(Horner.hornerInv(i, algSize, power)));
					gens.add(new IntArray(Horner.hornerInv(j, algSize, power)));
					gens.add(new IntArray(Horner.hornerInv(k, algSize, power)));
					Closer2 c1 = (new Closer2(bpa, gens, true)).setPassDecisionProcedure(Closer2.SERIAL).setStopEachPass(true);
					Closer2 c2 = (new Closer2(bpa, gens, true)).setPassDecisionProcedure(Closer2.PARALLEL).setStopEachPass(true);
					int passCounter = 0;
					while ( !c1.getCompleted() && !c2.getCompleted() ) {
						passCounter++;
						c1.sgClose();
						c2.sgClose();
						if ( !c1.equalCalculationStage(c2) ) {
							System.err.println("Error found.\nElements: ["+i+","+j+","+k+"]\nPass: "+passCounter);
							return false;
						} // end if ( !c1.equalCalculationStage(c2) )
						if ( passCounter>=1000000 ) {
							System.err.println("More than 1000000 passes.");
							return false;
						} // end if ( passCounter>=1000000 ) 
					} // end while ( !c1.getCompleted() && !c2.getCompleted() )
					System.out.println("Completed ["+i+","+j+","+k+"]");
				} // end j+1 <= k < productSize
			} // end i+1 <= j < productSize-1
		} // end for 0 <= i < productSize-2
		return true;
	} // end checkSubalgebraSet(SmallAlgebra,int)
	
	/**
	 * Defines what all the CLI commands do
	 * @return Whether or not to continue execution
	 */
	private boolean interpretCommand(String line) {
		StringTokenizer tok = new StringTokenizer(line);
		String command = null;
		String[] params = null;
		if ( tok.hasMoreTokens() ) {
			command = tok.nextToken();
		} else {
			return true;
		} // end if-else ( tok.hasMoreTokens() )
		params = new String[tok.countTokens()];
		for ( int i = 0; i < params.length; i++ ) {
			params[i]=tok.nextToken();
		} // end for 0 <= i < params.length
		if ( command.equalsIgnoreCase("help") || command.equalsIgnoreCase("?")) {
			System.out.println("\tHere is a list of available commands:");
			System.out.println("help\t\t\t\tThis command");
			System.out.println("?\t\t\t\tSame as help");
			System.out.println("quit\t\t\t\tCancels all tasks and quits the program");
			System.out.println("exit\t\t\t\tSame as quit");
			System.out.println("list\t\t\t\tLists all tasks");
			System.out.println("cancel <#>\t\t\tCancels task <#>");
			System.out.println("check <#>\t\t\tCheck on task <#>");
			System.out.println("algebras\t\t\tLists all algebras in memory");
			System.out.println("load <filename>\t\t\tLoads all algebras in <filename> into memory");
			System.out.println("remove <name>\t\t\tRemoves algebra <name> from memory");
			System.out.println("jonsson <name> [<#1>,[<#2>]]\t\t\tFinds Jonsson terms for algebra <name> (using <#1> CPUs and <#2> indices per chunk)");
			System.out.println("cancelafter <#1> <#2>\t\t\tCancels task <#1> after <#2> seconds.");
		} else if ( "quit".equalsIgnoreCase(command) || "exit".equalsIgnoreCase(command) ) {
			for ( int i = 0; i < tasks.size(); i++ ) {
				try {
					tasks.get(i).interrupt();
				} catch ( SecurityException e ) {
					System.out.println("Cannot cancel task "+i);
					e.printStackTrace(System.err);
				} // end try-catch (SecurityException)
			} // end for 0 <= i < tasks.size()
			return false;
		} else if ( "list".equalsIgnoreCase(command) ) {
			System.out.println("#\tType\tStatus");
			for ( int i = 0; i < tasks.size(); i++ ) {
				System.out.println(i+"\t"+taskTypes.get(i)+"\t"+(tasks.get(i).isAlive()?"Running":"Stopped"));
			} // end for 0 <= i < tasks.size()
		} else if ( "algebras".equalsIgnoreCase(command) ) {
			System.out.println("Name\tSize\tDescription");
			for ( String name : algs.keySet() ) {
				System.out.println(name+"\t"+algs.get(name).cardinality()+"\t"+algs.get(name).getDescription());
			} // end for name : algs.keySet()
		} else if ( "cancel".equalsIgnoreCase(command) ) {
			if ( params.length == 0 ) {
				System.out.println("Please specify a task to cancel.");
				return true;
			} // end if ( params.length == 0 )
			try {
				int i = Integer.valueOf(params[0]);
				tasks.get(i).interrupt();
				System.out.println("Task "+i+" cancelled.");
			} catch ( NumberFormatException e ) {
				System.out.println(params[0]+" is not a number.");
			} catch ( SecurityException f ) {
				System.out.println("Cannot cancel task "+params[0]);
				f.printStackTrace(System.err);
			} // end try-catch (NumberFormatException) (SecurityException)
		} else if ( "check".equalsIgnoreCase(command) ) {
			if ( params.length==0 ) {
				System.out.println("Please specify a task on which to check.");
				return true;
			} // end if ( params.length==0 )
			int i = -1;
			try {
				i = Integer.valueOf(params[0]);
			} catch ( NumberFormatException e ) {
				System.out.println(params[0]+" is not a number.");
				return true;
			} // end try-catch (NumberFormatException)
			if ( i<0 || i>tasks.size() ) {
				System.out.println("There is no task number "+i);
				return true;
			} // end if ( i<0 || i>tasks.size() )
			checkOn(i);
		} else if ( "load".equalsIgnoreCase(command) ) {
			if ( params.length==0 ) {
				System.out.println("Please specify a file to load.");
				return true;
			} // end if ( params.length==0 )
			Algebra temp = null;
			String[] maybeIn = new String[] {params[0], params[0]+".ua", ALGEBRA_DIR+params[0], ALGEBRA_DIR+params[0]+".ua"};
			boolean found = false;
			String fileName = null;
			for ( String fstr : maybeIn ) {
				try {
					if ( (new File(fstr)).exists() ) {
						found = true;
						fileName = fstr;
						break;
					} // end if ( (new File(fstr)).exists() )
				} catch ( SecurityException e ) {					
				} // end try-catch (SecurityException)
			} // end for ( String fstr : maybeIn )
			if ( !found ) {
				System.out.println("There is no file by that name.");
				return true;
			} // end if ( !found )
			try {
				temp = AlgebraIO.readAlgebraFile(fileName);
			} catch ( BadAlgebraFileException e ) {
				System.out.println(fileName+" is not an algebra file.");
			} catch ( IOException f ) {
				System.out.println("Something went wrong when reading the file.");
				f.printStackTrace(System.err);
			} // end try-catch (BadAlgebraFileException) (IOException)
			if ( temp!=null ) {
				String tempName = "A"+algs.size();
				algs.put(tempName, temp);
				algFiles.put(tempName,  fileName.indexOf("\\")!=-1?fileName.substring(fileName.lastIndexOf("\\")+1):fileName);
				System.out.println("Loaded algebra "+tempName);
			} // end if ( temp!=null )
		} else if ( "remove".equalsIgnoreCase(command) ) {
			if ( params.length==0 ) {
				System.out.println("Please specify an algebra to remove from memory.");
				return true;
			} // end if ( params.length==0 )
			if ( !algs.containsKey(params[0]) ) {
				System.out.println("There is no algebra by that name in memory.");
				return true;
			} // end if ( !algs.containsKey(params[0]) )
			algs.remove(params[0]);
			System.out.println("Removed algebra "+params[0]+" from memory.");
		} else if ( "jonsson".equalsIgnoreCase(command) ) {
			if ( params.length==0 ) {
				System.out.println("Please specify an algebra for which to calculate Jonsson operations.");
				return true;
			} // end if ( params.length==0 )
			if ( !algs.containsKey(params[0]) ) {
				System.out.println("There is no algebra by that name in memory.");
				return true;
			} // end if ( !algs.containsKey(params[0]) )
			int numThreads = 0;
			if ( params.length>=2 ) {				
				try {
					numThreads = Integer.valueOf(params[1]);
				} catch ( NumberFormatException e ) {
					System.out.println(params[1]+" is not a number, proceeding with 0.");
				} // try-catch NumberFormatException
			} // end if ( params.length>=2 )
			int indices = 1;
			if ( params.length>=3 ) {
				try {
					indices = Integer.valueOf(params[2]);
				} catch ( NumberFormatException e ) {
					System.out.println(params[2]+" is not a number, proceeding with 1");
				} // end try-catch NumberFormatException
			} // end if ( params.length>=3 )
			CLIProgressReport rep = null;
			try {
				rep = new CLIProgressReport(new PrintStream("jonsson-task-"+tasks.size()+".log")); 
			} catch ( FileNotFoundException e ) {
				e.printStackTrace(System.err);
			} // end try-catch (FileNotFoundException)
			Thread runner = new Thread(new JonssonRunner((SmallAlgebra)algs.get(params[0]),rep,numThreads,indices,"jonsson-partial-"+algFiles.get(params[0])+".termmap"));
			runner.setPriority(Thread.MAX_PRIORITY);
			reports.add(rep);
			tasks.add(runner);
			taskTypes.add("jonsson");
			runner.start();
			System.out.println("Started a Jonsson terms task on algebra "+params[0]);
		} else if ( "cancelafter".equalsIgnoreCase(command) ) {
			if ( params.length<2 ) {
				System.out.println("Syntax: cancelafter <#1> <#2>");
				return true;
			} // end if ( params.length<2 )
			int num = -1;
			int secs = -1;
			try {
				num = Integer.parseInt(params[0]);
			} catch ( NumberFormatException e ) {
				System.out.println(params[0]+" is not a number.");
				return true;
			} // end try-catch NumberFormatException
			try {
				secs = Integer.parseInt(params[1]);
			} catch ( NumberFormatException e ) {
				System.out.println(params[1]+" is not a number.");
				return true;
			} // end try-catch NumberFormatException
			Thread runner = new Thread(new CancelWaiter(num,secs));
			reports.add(null);
			tasks.add(runner);
			taskTypes.add("cancelafter");
			runner.start();
			System.out.println("Started a cancelAfter task on task "+num+".");
		} else {
			System.out.println("That is not a recognized command.");
		} // end switch (command)
		return true;
	} // end interpretCommand(String, String[])
	
	/**
	 * Cancels a task after a time.
	 * @author Jonah Horowitz
	 */
	private class CancelWaiter implements Runnable {
		private int target;
		private int secs;
		
		/**
		 * @param n The number of the task to cancel
		 * @param s The number of seconds to wait
		 */
		public CancelWaiter(int n, int s) {
			target=n;
			secs=s;
		} // end constructor()
		
		@Override
		public void run() {
			try {
				Thread.sleep(secs*1000);
			} catch ( InterruptedException e ) {}
			tasks.get(target).interrupt();
		} // end run()
	} // end class CancelWaiter
	
	/**
	 * Runs a search for Jonsson terms.
	 * @author Jonah Horowitz
	 */
	private class JonssonRunner implements Runnable {
		private SmallAlgebra alg;
		private CLIProgressReport report;
		private int numThreads;
		private int indicesPerChunk;
		private String saveFile;
		
		/**
		 * @param newAlg The algebra to search for Jonsson terms
		 * @param rep A means of reporting progress
		 * @param threads The number of threads to use 
		 * @param indices The number of indices per chunk
		 */
		public JonssonRunner(SmallAlgebra newAlg, CLIProgressReport rep, int threads, int indices, String partialSave) {
			alg=newAlg;
			report=rep;
			numThreads=threads;
			indicesPerChunk=indices;
			saveFile = partialSave;
		} // end constructor(SmallAlgebra, CLIProgressReport, int, int)
		
		@Override
		public void run() {
			List<Term> ans = Malcev.jonssonTerms(alg, false, report, numThreads, indicesPerChunk, saveFile);
			if ( report==null ) return;
			if ( ans==null ) {
				report.addLine("Returned null answer.");
				return;
			} // end if ( ans==null )
			for ( Term t : ans ) {
				report.addLine(t.toString());
			} // end for ( Term t : ans )
		} // end run()
	} // end class JonssonRunner
	
	/**
	 * Runs a very limited command line interface for UACalc.
	 */
	public void runCLI() {
		boolean keepGoing = true;
		String line = "";
		BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
		while ( keepGoing ) {
			try {
				System.out.print(">>> ");
				line = in.readLine();
				keepGoing = interpretCommand(line);
			} catch ( IOException e ) {
				e.printStackTrace(System.err);
			} // end try-catch (IOException)
		} // end while ( keepGoing )
	} // end runCLI()
	
	private static long calculateCloserTiming(Closer2 c) {
		long startTime = System.currentTimeMillis();
		c.sgClose();
		return System.currentTimeMillis()-startTime;
	} // end calculateCloserTiming(Closer2,BufferedWriter)
	
	private static class IncorrectAnswerException extends Exception {
		private static final long serialVersionUID=62;
		
		public IncorrectAnswerException(String message) {
			super(message);
		} // end constructor(String)
	} // end class IncorrectAnswerException
	
	/**
	 * Calculates a subuniverse several different ways and records the amount of time taken.
	 * @param alg  The algebra
	 * @param gens  The generators of the subuniverse
	 * @param makeTermMap  Whether or not to make the term map
	 * @param output  The file to which the times taken should be written
	 */
	public static void subalgebraTiming(Algebra alg, List<IntArray> gens, boolean makeTermMap, File output) throws IOException, IncorrectAnswerException {
		Set<IntArray> prev = null;
		long initialTime = -1;
		long startTime;
		if ( alg instanceof BigProductAlgebra )	{
			Closer prev2 = new Closer((BigProductAlgebra)alg,gens,makeTermMap);
			startTime = System.currentTimeMillis();
			prev = new HashSet<IntArray>(prev2.sgClose());
			initialTime = System.currentTimeMillis()-startTime;
		} // end if ( alg instanceof BigProductAlgebra )		
		int numCPUs = Runtime.getRuntime().availableProcessors();
		Closer2[] parallel = new Closer2[2*numCPUs];
		parallel[0] = new Closer2(alg,gens,makeTermMap).setPassDecisionProcedure(Closer2.SERIAL).setStopEachPass(true);
		for ( int i = 1; i < parallel.length; i++ ) parallel[i] = new Closer2(alg,gens,makeTermMap).setPassDecisionProcedure(Closer2.PARALLEL).setNumThreads(i+1).setStopEachPass(true);
		Closer2[] ewl = new Closer2[2*numCPUs];
		for ( int i = 0; i < ewl.length; i++ ) ewl[i] = new Closer2(alg,gens,makeTermMap).setPassDecisionProcedure(Closer2.EQUAL_WORKLOAD).setNumThreads(i+1).setStopEachPass(true);
		Closer2[] parallelNP = new Closer2[parallel.length];
		parallelNP[0] = new Closer2(alg,gens,makeTermMap).setPassDecisionProcedure(Closer2.SERIAL).setStopEachPass(true).setForceNonPower(true);
		for ( int i = 1; i < parallelNP.length; i++ ) parallelNP[i] = new Closer2(alg,gens,makeTermMap).setPassDecisionProcedure(Closer2.PARALLEL).setNumThreads(i+1).setStopEachPass(true).setForceNonPower(true);
		Closer2[] ewlNP = new Closer2[ewl.length];
		for ( int i = 0; i < ewlNP.length; i++ ) ewlNP[i] = new Closer2(alg,gens,makeTermMap).setPassDecisionProcedure(Closer2.EQUAL_WORKLOAD).setNumThreads(i+1).setStopEachPass(true).setForceNonPower(true);/**/
		if (!output.exists()) output.createNewFile();
		BufferedWriter out = new BufferedWriter(new FileWriter(output));
		out.write("Algebra name: "+alg.getName()+"\nNumber of Cores:;"+numCPUs+"\nSubuniverse Generators:");
		for ( IntArray ia : gens ) out.write(";"+ia.toString());
		String headers = "\nBaseline time;"+initialTime+"\nType;Threads";
		String passSizes = "Pass Sizes:";
		int pass = 0;
		String ans = "Serial;1";
		while (!parallel[0].getCompleted()) {
			System.out.println("Calculating "+alg.getName()+", type serial, pass "+parallel[0].getPass());
			headers=headers+";"+pass;
			passSizes = passSizes+";"+(parallel[0].getAnswer()==null?gens.size():parallel[0].getAnswer().size());
			ans=ans+";"+calculateCloserTiming(parallel[0]);
		} // end while (!parallel[0].getCompleted())
		if ( prev!=null && !prev.equals(new HashSet<IntArray>(parallel[0].getAnswer())) ) {
			String blah = "Error calculating "+alg.getName()+", type serial: Result mismatch.";
			System.err.println(blah);
			out.close();
			throw new IncorrectAnswerException(blah);
		} // end if ( prev!=null && !prev.equals(new HashSet<IntArray>(parallel[0].getAnswer())) )
		out.write(passSizes+"\n"+headers+"\n"+ans+"\n");
		ans = "Serial-NP;1";
		while (!parallelNP[0].getCompleted()) {
			System.out.println("Calculating "+alg.getName()+", type serialNP, pass "+parallelNP[0].getPass());
			ans=ans+";"+calculateCloserTiming(parallelNP[0]);
		} // end while (!parallelNP[0].getCompleted())
		if ( prev!=null && !prev.equals(new HashSet<IntArray>(parallelNP[0].getAnswer())) ) {
			String blah="Error calculating "+alg.getName()+", type serialNP: Result mismatch.";
			System.err.println(blah);
			out.close();
			throw new IncorrectAnswerException(blah);
		} // end if ( prev!=null && !prev.equals(new HashSet<IntArray>(parallel[0].getAnswer())) )/**/
		out.write(ans+"\n");
		for ( int i = 1; i < parallel.length; i++ ) {
			ans="Parallel;"+(i+1);
			while (!parallel[i].getCompleted()) {
				System.out.println("Calculating "+alg.getName()+", type parallel ("+(i+1)+"), pass "+parallel[i].getPass());
				ans=ans+";"+calculateCloserTiming(parallel[i]);
			} // end while (!parallel[i].getCompleted())
			if ( prev!=null && !prev.equals(new HashSet<IntArray>(parallel[i].getAnswer())) ) {
				String blah="Error calculating "+alg.getName()+", type parallel ("+(i+1)+"): Result mismatch.";
				System.err.println(blah);
				out.close();
				throw new IncorrectAnswerException(blah);
			} // end if ( prev!=null && !prev.equals(new HashSet<IntArray>(parallel[0].getAnswer())) )
			out.write(ans+"\n");
		} // end for 1 <= i < parallel.length
		for ( int i = 1; i < parallelNP.length; i++ ) {
			ans="Parallel-NP;"+(i+1);
			while (!parallelNP[i].getCompleted()) {
				System.out.println("Calculating "+alg.getName()+", type parallelNP ("+(i+1)+"), pass "+parallelNP[i].getPass());
				ans=ans+";"+calculateCloserTiming(parallelNP[i]);
			} // end while (!parallel[i].getCompleted())
			if ( prev!=null && !prev.equals(new HashSet<IntArray>(parallelNP[i].getAnswer())) ) {
				String blah="Error calculating "+alg.getName()+", type parallelNP ("+(i+1)+"): Result mismatch.";
				System.err.println(blah);
				out.close();
				throw new IncorrectAnswerException(blah);
			} // end if ( prev!=null && !prev.equals(new HashSet<IntArray>(parallel[0].getAnswer())) )
			out.write(ans+"\n");
		} // end for 1 <= i < parallel.length/**/
		for ( int i = 0; i < ewl.length; i++ ) {
			ans="EWL;"+(i+1);
			while (!ewl[i].getCompleted()) {		
				System.out.println("Calculating "+alg.getName()+", type EWL ("+(i+1)+"), pass "+ewl[i].getPass());
				ans=ans+";"+calculateCloserTiming(ewl[i]);
			} // end while (!ewl[i].getCompleted())
			out.write(ans+"\n");
			if ( prev!=null && !prev.equals(new HashSet<IntArray>(ewl[i].getAnswer())) ) {
				String blah="Error calculating "+alg.getName()+", type EWL ("+(i+1)+"): Result mismatch.";
				System.err.println(blah);
				out.close();
				throw new IncorrectAnswerException(blah);
			} // end if ( prev!=null && !prev.equals(new HashSet<IntArray>(parallel[0].getAnswer())) )
		} // end for 0 <= i < ewl.length
		for ( int i = 0; i < ewlNP.length; i++ ) {
			ans="EWL-NP;"+(i+1);
			while (!ewlNP[i].getCompleted()) {		
				System.out.println("Calculating "+alg.getName()+", type EWLNP ("+(i+1)+"), pass "+ewlNP[i].getPass());
				ans=ans+";"+calculateCloserTiming(ewlNP[i]);
			} // end while (!ewl[i].getCompleted())
			if ( prev!=null && !prev.equals(new HashSet<IntArray>(ewlNP[0].getAnswer())) ) {
				String blah="Error calculating "+alg.getName()+", type EWLNP ("+(i+1)+"): Result mismatch.";
				System.err.println(blah);
				out.close();
				throw new IncorrectAnswerException(blah);
			} // end if ( prev!=null && !prev.equals(new HashSet<IntArray>(parallel[0].getAnswer())) )
			out.write(ans+"\n");
		} // end for 0 <= i < ewl.length/**/
		out.close();
	} // end subalgebraTiming(Algebra,List<IntArray>,File)

	/**
	 * Represents a pair.
	 * @author Jonah Horowitz
	 *
	 * @param <A>  The class of the first element
	 * @param <B>  The class of the second element
	 */
	private static class Pair<A,B> {
		private A first;
		private B second;
		
		public Pair(A a, B b) {
			first=a;
			second=b;
		} // end constructor(A,B)
		
		public A getFirst() { return first; }
		public B getSecond() { return second; }
	} // end class Pair<A,B>
	
	public static Pair<SmallAlgebra,String> loadBuiltin(String name) {
		String fileName = "algebras/" + name + ".ua";
		ClassLoader cl = Horowitz.class.getClassLoader();
		InputStream is = cl.getResourceAsStream(fileName);
		SmallAlgebra alg = null;
		try {
			alg = AlgebraIO.readAlgebraFromStream(is);
		} catch ( BadAlgebraFileException e ) {
			e.printStackTrace();
		} catch ( IOException f ) {
			f.printStackTrace();
		} // end try-catch BadAlgebraFileException IOException
		return new Pair<SmallAlgebra,String>(alg,name);
	} // end loadBuiltin(String)
	
	/**
	 * Loads all the algebras which are by default in the resources\algebras directory
	 * @return  A list consisting of algebra, filename pairs.
	 */
	public static List<Pair<SmallAlgebra,String>> loadAllAlgebras() {
		List<Pair<SmallAlgebra,String>> ans = new ArrayList<Pair<SmallAlgebra,String>>();
/*			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\ba2.ua"),"ba2"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\baker2.ua"),"baker2"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\baker2withtop.ua"),"baker2withtop"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\cyclic2.ua"),"cyclic2"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\cyclic3.ua"),"cyclic3"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\d16.ua"),"d16"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\diffi.ua"),"diffi"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\hajilarov.ua"),"hajilarov"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\lat2-01.ua"),"lat2-01"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\lat2.ua"),"lat2"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\lyndon.ua"),"lyndon"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\m3.ua"),"m3"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\m4.ua"),"m4"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\n5.ua"),"n5"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\polin.ua"),"polin"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\sym3.ua"),"sym3"));
			ans.add(new Pair<SmallAlgebra,String>(AlgebraIO.readAlgebraFile("resources\\algebras\\z3.ua"),"z3"));/**/			
		ans.add(loadBuiltin("ba2"));
		ans.add(loadBuiltin("baker2"));
		ans.add(loadBuiltin("baker2withtop"));
		ans.add(loadBuiltin("cyclic2"));
		ans.add(loadBuiltin("cyclic3"));
//		ans.add(loadBuiltin("d16"));
		ans.add(loadBuiltin("diffi"));
		ans.add(loadBuiltin("hajilarov"));
		ans.add(loadBuiltin("lat2-01"));
		ans.add(loadBuiltin("lat2"));
		ans.add(loadBuiltin("lyndon"));
		ans.add(loadBuiltin("m3"));
		ans.add(loadBuiltin("m4"));
		ans.add(loadBuiltin("n5"));
		ans.add(loadBuiltin("polin"));
//		ans.add(loadBuiltin("sym3"));
		ans.add(loadBuiltin("z3"));
		return ans;
	} // end loadAllAlgebras()

	public static void runJonssonTimeTrials() {
		final String outD = "timeTrials-Jonsson";
		long startTime = System.currentTimeMillis();
		File outDir = new File(outD);
		if (!outDir.exists()) outDir.mkdir();
		List<Pair<SmallAlgebra,String>> algs = loadAllAlgebras();
		List<IntArray> gens = new ArrayList<IntArray>(3);
		gens.add(new IntArray(new int[] {0,0,1}));
		gens.add(new IntArray(new int[] {0,1,0}));
		gens.add(new IntArray(new int[] {1,0,0}));
		String wasError=null;
		for ( Pair<SmallAlgebra,String> p : algs ) {
			File output = new File(outD+"\\"+p.getSecond()+".csv");
			FreeAlgebra f2 = new FreeAlgebra(p.getFirst(),2);
			f2.makeOperationTables();
			BigProductAlgebra bpa = new BigProductAlgebra("f("+p.getSecond()+")",f2,3);
			try {
				subalgebraTiming(bpa,gens,true,output);
			} catch ( IOException e ) {
				e.printStackTrace();
			} catch ( IncorrectAnswerException f ) {
				wasError=f.getMessage();
			} // end try-catch IOException IncorrectAnswerException
		} // end for ( Pair<SmallAlgebra,String> p : algs )
/*		for ( int i = 0; i < algs.size(); i++ ) {
			for ( int j = i; j < algs.size(); j++ ) {
			} // end for i <= j < algs.size()
		} // end for 0 <= i < algs.size()/**/
		File logFile = new File(outD+"\\logfile.txt");
		try {
			if (!logFile.exists()) logFile.createNewFile();
			BufferedWriter outLog = new BufferedWriter(new FileWriter(logFile));
			if (wasError!=null) outLog.write(wasError+"\n");
			outLog.write("Total time taken: "+(System.currentTimeMillis()-startTime));
			outLog.close();
		} catch ( IOException e ) {
			e.printStackTrace();
		} // end try-catch IOException
	} // end runTimeTrials()
	
	public static void main(String[] args) {
		runJonssonTimeTrials();
		
/*		SmallAlgebra ba2 = null;
		try {
			ba2 = AlgebraIO.readAlgebraFile("resources\\algebras\\ba2.ua");
		} catch ( BadAlgebraFileException e ) {
			e.printStackTrace();
		} catch ( IOException f ) {
			f.printStackTrace();
		} // end try-catch BadAlgebraFileException IOException
		FreeAlgebra f2 = new FreeAlgebra(ba2,2);
		f2.makeOperationTables();
		BigProductAlgebra bpa = new BigProductAlgebra("f(ba2)",f2,3);
		List<IntArray> gens = new ArrayList<IntArray>(3);
		gens.add(new IntArray(new int[] {0,0,1}));
		gens.add(new IntArray(new int[] {0,1,0}));
		gens.add(new IntArray(new int[] {1,0,0}));
		
		Closer2 serial = new Closer2(bpa,gens,true).setPassDecisionProcedure(Closer2.SERIAL).setStopEachPass(true);
		Closer2 serialNP = new Closer2(bpa,gens,true).setPassDecisionProcedure(Closer2.SERIAL).setStopEachPass(true).setForceNonPower(true);
		while (!serial.getCompleted() && !serialNP.getCompleted()) {
			serialNP.sgClose();
			serial.sgClose();
			System.out.println("Sizes: "+serial.getAnswer().size()+" -- "+serialNP.getAnswer().size());
		} // end while (!serial.getCompleted() && !serialNP.getCompleted())/**/
		
/*		SmallAlgebra alg = null;
		try {
			alg = AlgebraIO.readAlgebraFile("resources\\algebras\\n5.ua");
		} catch ( BadAlgebraFileException e ) {
			e.printStackTrace();
		} catch ( IOException f ) {
			f.printStackTrace();
		} // end try-catch BadAlgebraFileException, IOException
		File output = new File("C:\\Users\\Yiab\\Desktop\\ua\\n5p5v1.csv");
		BigProductAlgebra bpa = new BigProductAlgebra("n5^5",alg,5);
		List<IntArray> gens = new ArrayList<IntArray>();
		gens.add(new IntArray(new int[] {1,0,0,0,0}));
		gens.add(new IntArray(new int[] {0,1,0,0,0}));
		gens.add(new IntArray(new int[] {0,0,1,0,0}));
		gens.add(new IntArray(new int[] {0,0,0,1,0}));
		gens.add(new IntArray(new int[] {0,0,0,0,1}));/**/
/*		Closer2 ewl = new Closer2(bpa,gens,true).setPassDecisionProcedure(Closer2.EQUAL_WORKLOAD).setNumThreads(1).setStopEachPass(true);
		while (!ewl.getCompleted()) {
			System.out.println("Pass "+ewl.getPass()+", time: "+calculateCloserTiming(ewl));			
		} // end while (!ewl.getCompleted())/**/
/*		try {
			subalgebraTiming(bpa,gens,true,output);
		} catch ( IOException e ) {
			e.printStackTrace();
		}/**/
//		if ( alg!=null ) System.out.println("Result: "+check3GeneratedSubalgebras(alg,1));/**/
		
//		(new Horowitz()).runCLI();
/*		Vector<Operation> ops = new Vector();
		ops.addAll(makeFlatAlmostJonssonSequence(3,4,new int[] {0,1,0},2));
		ops.add(makeFlatAlmostJonssonOperation("d21012",3,2,false,new int[] {1,0,1},2));
		BasicAlgebra alg = new BasicAlgebra("A3",3,ops);/**/
//		BasicAlgebra alg = makeFlatAlmostJonssonAlgebra( "A1", 3, 4 );
/*		try {
			if (HasKaryNU.hasNUHorowitz(alg, 3)==1) {
				System.out.println("Has a majority term.");
			} else if (HasKaryNU.hasNUHorowitz(alg, 4)==1) {
				System.out.println("Has a 4-ary NU term.");
			} else if (HasKaryNU.hasNUHorowitz(alg, 5)==1) {
				System.out.println("Has a 5-ary NU term.");
			} else {
				System.out.println("Has no 5-ary NU term.");
			}
		} catch ( IOException e ) {
			System.err.println(e);
		}/**/
/*		try {
			AlgebraIO.writeAlgebraFile(alg, "resources\\algebras\\smallFlatAlmostJonsson2.ua");
			System.out.println("Written algebra to file.");
		} catch ( IOException e ) {
			System.err.println(e);
		}/**/
		//System.out.println(Malcev.jonssonTerms(alg));
/*		try {
			AlgebraIO.writeAlgebraFile(alg,"resources\\algebras\\flatAlmostJonsson.ua");
			System.out.println("Written algebra.");
		} catch ( IOException e ) {
			System.err.println(e);
		}
		System.out.println("Done.");
		
/*		BasicAlgebra alg = makeRandomAlmostJonssonAlgebra( "A1", 3, 4 );
		try {
			AlgebraIO.writeAlgebraFile(alg, "A1.ua");
			System.out.println("Written to A1.ua.");
			if (HasKaryNU.hasNUHorowitz(alg, 3)==1) {
				System.out.println("Has a majority term.");
			} else if (HasKaryNU.hasNUHorowitz(alg, 4)==1) {
				System.out.println("Has a 4-ary NU term.");
			}
			System.out.println(Malcev.jonssonTerms(alg));
		} catch ( Exception e ) {
			System.err.println(e);
		}/**/
		
/*		for ( int i = 0; i < 10000; i++ ) {
			BasicAlgebra alg = makeRandomAlmostJonssonAlgebra( "A"+i, 3, 4);
			System.out.println("Working on Algebra #: "+i);
			try {
				if (HasKaryNU.hasNUHorowitz(alg, 3)==0) {
					AlgebraIO.writeAlgebraFile(alg, "A"+i+".ua");
					System.out.println("Found one!");
					break;
				}
			} catch ( Exception e ) {
				System.err.println(e);
			}
		}/**/
		System.out.println("Done.");
	}
}