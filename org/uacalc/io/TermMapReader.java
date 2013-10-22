package org.uacalc.io;

import java.util.*;
import org.uacalc.util.IntArray;
import org.uacalc.terms.*;
import java.io.*;
import org.uacalc.alg.op.OperationSymbol;

/**
 * Reads in tab-delimited term map files.
 * @author Jonah Horowitz
 */
public class TermMapReader {
	public static Map<IntArray,Term> readTermMap(String fileName) throws FileNotFoundException {
		return readTermMap(new BufferedReader(new FileReader(fileName)));
	} // end readTermMap(String)
	
	public static Map<IntArray,Term> readTermMap(File target) throws FileNotFoundException {
		return readTermMap(new BufferedReader(new FileReader(target)));
	} // end readTermMap(File)
	
	public static Map<IntArray,Term> readTermMap(BufferedReader in) {
		String[] line = new String[2];
		Map<IntArray,Term> termMap = new HashMap<IntArray,Term>();
		while (true) {
			try {
				line = in.readLine().split("\t");
				termMap.put(new IntArray(IntArray.stringToArray(line[0])), parseTerm(line[1]));
			} catch ( IOException e ) {
				break;
			} catch ( ArrayIndexOutOfBoundsException f ) {				
			} // end try-catch IOException ArrayIndexOutOfBoundsException
		} // end while (true)
		return termMap;
	} // end readTermMap(BufferedReader)
	
	public static Term parseTerm(String target) {
		if ( target==null || target.length()==0 ) return null;
		if ( target.indexOf(NonVariableTerm.LEFT_PAR)==-1 ) return new VariableImp(target);
		String head = target.substring(0, target.indexOf(NonVariableTerm.LEFT_PAR));
		List<Term> body = parseTermList(target.substring(target.indexOf(NonVariableTerm.LEFT_PAR)+1, target.lastIndexOf(NonVariableTerm.RIGHT_PAR)));
		return new NonVariableTerm(new OperationSymbol(head,body.size()),body);
	} // end parseTerm(String)
	
	public static List<Term> parseTermList(String target) {
		List<Term> ans = new ArrayList<Term>();
		int startIndex = 0;
		int endIndex = 0;
		int bracketDepth=0;
		while ( endIndex<target.length() ) {
			switch ( target.charAt(endIndex) ) {
				case '(': bracketDepth++; break;
				case ')': bracketDepth--; break;
				case ',': if ( bracketDepth==0 ) {
					Term temp = parseTerm(target.substring(startIndex, endIndex)); 
					if ( temp!=null ) ans.add(temp);
					startIndex=endIndex+1;
				} // end if ( bracketDepth==0 )
			} // end switch ( target.charAt(endIndex) )
			endIndex++;
		} // end while ( startIndex<target.length() )
		if ( bracketDepth==0 ) {
			Term temp = parseTerm(target.substring(startIndex));
			if ( temp!=null ) ans.add(temp);
		} // end if ( bracketDepth==0 )
		return ans;
	} // end parseTermList(String)
	
	public static void main(String[] args) {
		for ( String x : args ) {
			System.out.println(x+": "+parseTerm(x).toString());
		}
	}
} // end class TermMapReader
