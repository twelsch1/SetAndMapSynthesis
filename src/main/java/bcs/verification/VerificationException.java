package bcs.verification;

/**
 * A custom Exception used by the Verifier class. If this Exception is seen means an error was encountered during verification.
 * @author Thomas Welsch
 *
 */
public class VerificationException extends Exception {

	private static final long serialVersionUID = -4910213921113744412L;
	
	/**
	 * A constructor that simply calls the super constructor of Exception with the message as a parameter.
	 * @param message Message to set in Exception indicating reason for failure.
	 */
	public VerificationException(String message) {
		super(message);
	}
	
	

}
