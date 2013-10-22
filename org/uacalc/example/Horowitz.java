package org.uacalc.example;

import org.uacalc.alg.op.*;
import org.uacalc.alg.*;

import java.util.*;

import org.uacalc.util.Horner;
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
	
	public static void main(String[] args) {
		(new Horowitz()).runCLI();
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