package org.uacalc.ui.tm;

import java.io.PrintStream;
import java.util.concurrent.Semaphore;

/**
 * Replaces <code>org.uacalc.ui.tm.ProgressReport</code> when dealing with command line interfaces
 * @author Jonah Horowitz
 */
public class CLIProgressReport extends ProgressReport {
	private PrintStream out;
	private int pass = -1;
	private Semaphore passLock = new Semaphore(1);
	private int passSize = -1;
	private Semaphore passSizeLock = new Semaphore(1);
	private int size = -1;
	private Semaphore sizeLock = new Semaphore(1);
	private String timeLeft = "";
	private Semaphore timeLeftLock = new Semaphore(1);
	private String timeNext = "";
	private Semaphore timeNextLock = new Semaphore(1);
	
	/**
	 * @param newOut The <code>java.io.PrintStream</code> to which to output
	 */
	public CLIProgressReport(PrintStream newOut) {
		super();
		if ( newOut!=null ) {
			out = newOut;
		} else {
			out = System.out;
		}
	} // end constructor(PrintStream)
	
	@Override
	public String getTimeNext() {
		String temp = null;
		timeNextLock.acquireUninterruptibly();
		temp = timeNext;
		timeNextLock.release();
		return temp;
	} // end getTimeNext()
	
	@Override
	public void setTimeNext(String time) {
		timeNextLock.acquireUninterruptibly();
		timeNext = time;
		timeNextLock.release();
	} // end setTimeNext(String)
	
	@Override
	public String getTimeLeft() {
		String temp = null;
		timeLeftLock.acquireUninterruptibly();
		temp = timeLeft;
		timeLeftLock.release();
		return temp;
	} // end getTimeLeft()
	
	@Override
	public void setTimeLeft(String time) {
		timeLeftLock.acquireUninterruptibly();
		timeLeft = time;
		timeLeftLock.release();
	} // end setTimeLeft(String)
	
	@Override
	public void addEndingLine(final String line) {
		out.println(line);
	} // end addEndingLine(String)
	
	@Override
	public int getSize() {
		int temp = -1;
		sizeLock.acquireUninterruptibly();
		temp = size;
		sizeLock.release();
		return temp;
	} // end getSize()
	
	@Override
	public void setSize(int n) {
		sizeLock.acquireUninterruptibly();
		size=n;
		sizeLock.release();
	} // end setSize(int)
	
	@Override
	public void addLine(final String line) {
		out.println(line);
	} // end addLine(String)
	
	@Override
	public int getPassSize() {
		int temp = -1;
		passSizeLock.acquireUninterruptibly();
		temp = passSize;
		passSizeLock.release();
		return temp;
	} // end getPassSize()
	
	@Override
	public void setPassSize(int n) {
		passSizeLock.acquireUninterruptibly();
		passSize=n;
		passSizeLock.release();
	} // end setPassSize(int)
	
	@Override
	public void addStartLine(final String line) {
		out.println(line);
	} // end addStartLine(String)
	
	@Override
	public void setPass(int n) {
		passLock.acquireUninterruptibly();
		pass=n;
		passLock.release();
	} // end setPass(int)
	
	@Override
	public int getPass() {
		int temp = -1;
		passLock.acquireUninterruptibly();
		temp = pass;
		passLock.release();
		return temp;
	} // end getPass()

} // end class CLIProgressReport
