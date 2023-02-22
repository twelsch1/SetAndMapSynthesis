package bcs.jobs;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class SCJobResult {

	private boolean successful;
	private SplitAndConquerProgramSynthesis parentJob;
	private SplitAndConquerProgramSynthesis[] children = null;
	private String program;
	
	public SCJobResult(boolean successful, SplitAndConquerProgramSynthesis parentJob, SplitAndConquerProgramSynthesis[] children, String program) {
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

	public SplitAndConquerProgramSynthesis getParentJob() {
		return parentJob;
	}

	public void setParentJob(SplitAndConquerProgramSynthesis parentJob) {
		this.parentJob = parentJob;
	}

	public SplitAndConquerProgramSynthesis[] getChildren() {
		return children;
	}

	public void setChildren(SplitAndConquerProgramSynthesis[] children) {
		this.children = children;
	}


	public String getProgram() {
		return program;
	}


	public void setProgram(String program) {
		this.program = program;
	}
	
	
	
	
	
	
}
