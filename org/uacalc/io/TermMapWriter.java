package org.uacalc.io;

import org.uacalc.util.IntArray;
import java.util.*;
import org.uacalc.terms.Term;
import java.io.*;

/**
 * Since I can't figure out SAX by inspecting <code>org.uacalc.io.AlgebraReader</code>, 
 * this class will write a <code>java.util.Map<org.uacalc.util.IntArray,org.uacalc.terms.Term></code> as a sequence of lines,
 * each of which is a tab-delimited pairs of int array, followed by the term.
 * @author Jonah Horowitz
 */
public class TermMapWriter {
	public static void writeTermMap(Map<IntArray,Term> termMap, String fileName) throws FileNotFoundException {
		writeTermMap(termMap, new PrintStream(fileName));
	} // end writeTermMap(Map<IntArray,Term>, String)
	
	public static void writeTermMap(Map<IntArray,Term> termMap, File target) throws FileNotFoundException {
		writeTermMap(termMap, new PrintStream(target));
	} // end writeTermMap(Map<IntArray,Term>, File)

	/**
	 * Writes <code>termMap</code> to the given <code>PrintStream</code> 
	 */
	public static void writeTermMap(Map<IntArray,Term> termMap, PrintStream out) {
		if ( termMap==null || out==null ) return;
		for ( IntArray v : termMap.keySet() ) {
			out.println(v.toString()+"\t"+termMap.get(v).toString());
		} // end for ( IntArray v : keySet )
	} // end writeTermMap(Map<IntArray,Term>, PrintStream)
} // end class TermMapWriter
