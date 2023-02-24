package bcs.jobs;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class SCJobResult {

	private boolean successful;
	private SplitAndCoverProgramSynthesis parentJob;
	private SplitAndCoverProgramSynthesis[] children = null;
	private String program;
	
	public SCJobResult(boolean successful, SplitAndCoverProgramSynthesis parentJob, SplitAndCoverProgramSynthesis[] children, String program) {
		this.successful = successful;
		this.parentJob = parentJob;
		this.children = children;
		this.program = program;
	}


	public boolean isSuccessful() {
		return successful;
	}

	public void setSuccessful(boolean successful) {
		this.successful = successful;
	}

	public SplitAndCoverProgramSynthesis getParentJob() {
		return parentJob;
	}

	public void setParentJob(SplitAndCoverProgramSynthesis parentJob) {
		this.parentJob = parentJob;
	}

	public SplitAndCoverProgramSynthesis[] getChildren() {
		return children;
	}

	public void setChildren(SplitAndCoverProgramSynthesis[] children) {
		this.children = children;
	}


	public String getProgram() {
		return program;
	}


	public void setProgram(String program) {
		this.program = program;
	}
	
	
	
	
	
	
}
