package sms.synthesizer;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class SynthesisResult {

	private boolean successful = false;
	private String programFound;
	private long timeTaken = 0;
	private String split;

	
	
	public SynthesisResult(boolean wasSuccessful, String programFound, String split) {
		this.successful = wasSuccessful;
		this.programFound = programFound;
		this.split = split;

	}
	
	
	public SynthesisResult(boolean wasSuccessful, String programFound) {
		this.successful = wasSuccessful;
		this.programFound = programFound;
	}
	
	
	public SynthesisResult(boolean wasSuccessful, String programFound, long timeTaken) {

		this.successful = wasSuccessful;
		this.programFound = programFound;
		this.timeTaken = timeTaken;
	}
	

	public boolean isSuccessful() {
		return successful;
	}
	public void setSuccessful(boolean wasSuccessful) {
		this.successful = wasSuccessful;
	}
	public String getProgramFound() {
		return programFound;
	}
	public void setProgramFound(String programFound) {
		this.programFound = programFound;
	}
	public long getTimeTaken() {
		return timeTaken;
	}
	public void setTimeTaken(long timeTaken) {
		this.timeTaken = timeTaken;
	}
	public String getSplit() {
		return split;
	}
	public void setSplit(String split) {
		this.split = split;
	}
	
	public String asResultString() {
		return this.successful + "," + this.timeTaken + "," + this.programFound.length();
	}

	
	
	
	
}
