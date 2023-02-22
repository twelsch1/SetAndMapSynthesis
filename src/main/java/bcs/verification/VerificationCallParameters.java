package bcs.verification;

import java.util.ArrayList;

import com.microsoft.z3.Context;

/**
 * A class containing parameters that are passed onto the verification calls.
 * @author Thomas Welsch
 *
 */
public class VerificationCallParameters {

	/**
	 * An ArrayList of CounterExamples, if provided these are excluded during verification. Prevents duplicate examples being found
	 * but means correctness is not guaranteed, so this should only be included in calls where it is known the program to verify is incorrect.
	 */
	private ArrayList<CounterExample> counterExamples = null;
	/**
	 * The timeout integer passed through to the verification call, it corresponds to the number of milliseconds the verification call
	 * is allowed before it returns. If this is set to -1 then there is no timeout.
	 */
	private int timeout;
	/**
	 * The number of threads passed to the Z3 call.
	 */
	private int threads;
	
	private Context context;
	
	public VerificationCallParameters() {
		timeout = -1;
		threads = 1;
	}
	public VerificationCallParameters(ArrayList<CounterExample> counterExamples, int timeout, int threads, Context context) {
		this.counterExamples = counterExamples;
		this.timeout = timeout;
		this.threads = threads;
		this.context = context;
	}
	
	public VerificationCallParameters(ArrayList<CounterExample> counterExamples, int timeout, int threads) {
		this.counterExamples = counterExamples;
		this.timeout = timeout;
		this.threads = threads;
	}
	public ArrayList<CounterExample> getCounterExamples() {
		return counterExamples;
	}
	public void setCounterExamples(ArrayList<CounterExample> counterExamples) {
		this.counterExamples = counterExamples;
	}
	public int getTimeout() {
		return timeout;
	}
	public void setTimeout(int timeout) {
		this.timeout = timeout;
	}
	public int getThreads() {
		return threads;
	}
	public void setThreads(int threads) {
		this.threads = threads;
	}
	public Context getContext() {
		return context;
	}
	public void setContext(Context context) {
		this.context = context;
	}
	
	
	
	
	
	
	
	
	
}
