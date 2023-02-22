package bcs.optional;

import java.util.ArrayList;
import java.util.concurrent.Callable;

import bcs.verification.CounterExample;
import bcs.verification.VerificationCallParameters;
import bcs.verification.VerificationResult;
import bcs.verification.Verifier;

/**
 * An optional implementation of a Callable that can be used to make verification calls in parallel.
 * @author Thomas Welsch
 *
 */
public class VerificationCallable implements Callable<VerificationResult>  {

	/**
	 * The program to verify
	 */
	private String program;
	/**
	 * The verifier to use for verification.
	 */
	private Verifier verifier;
	/**
	 * Any counterExamples that have been previously found.
	 */
	private ArrayList<CounterExample> counterExamples;
	/**
	 * The time in milliseconds to allow for the verification call.
	 */
	private int timeout;
	
	/**
	 * A standard Constructor, sets internal values in the class based off parameters, also sets the timeout to be -1 i.e. unlimited.
	 * @param program The program to verify.
	 * @param verifier The verifier to use for verification.
	 * @param counterExamples CounterExamples that have been previously found.
	 */
	public VerificationCallable(String program, Verifier verifier,
			ArrayList<CounterExample> counterExamples) {
		this.program = program;
		this.verifier = verifier;
		this.counterExamples = counterExamples;
		this.timeout = -1;
	}
	
	/**
	 * A standard Constructor, sets internal values in the class based off parameters.
	 * @param program The program to verify.
	 * @param verifier The verifier to use for verification.
	 * @param counterExamples CounterExamples that have been previously found.
	 * @param timeout The time in milliseconds to allow for the verification call.
	 */
	public VerificationCallable(String program, Verifier verifier, ArrayList<CounterExample> counterExamples,
			int timeout) {
		this.program = program;
		this.verifier = verifier;
		this.counterExamples = counterExamples;
		this.timeout = timeout;
	}	
	
	/**
	 * Verifies the program.
	 * @return The VerificationResult obtained from the verification attempt.
	 */
	@Override
	public VerificationResult call() throws Exception {

		VerificationCallParameters vcp = new VerificationCallParameters();
		vcp.setTimeout(timeout);
		vcp.setCounterExamples(counterExamples);
		
		return verifier.verify(program, vcp);

	}


}
