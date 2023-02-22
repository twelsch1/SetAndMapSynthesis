package bcs.jobs;

import bcs.synthesizer.SynthesisResult;
import bcs.synthesizer.Synthesizer;
import bcs.verification.Verifier;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class SplitAndConquerProgramSynthesis implements Comparable<SplitAndConquerProgramSynthesis> {
	
	
	private String[] extraAssertions; //the constraints on the input space derived from direct ancestors
	private int tiebreaker; //used as a tiebreaker for job priority, 0 is RHS, 1 is LHS, 2 is root, we prioritize highest
	private int restarts = 0;
	
	
	
	
	public SplitAndConquerProgramSynthesis(String[] extraAssertions, int tiebreaker, int restarts) {
		this.extraAssertions = extraAssertions;
		this.tiebreaker = tiebreaker;	
		this.restarts = restarts;

	}

	public SynthesisResult run(Verifier verifier, Synthesizer partialsSynthesizer) {
		return partialsSynthesizer.synthesize(verifier);
	}
	
	public SplitAndConquerProgramSynthesis[] split(String pred) {
		   SplitAndConquerProgramSynthesis[] childJobs = new SplitAndConquerProgramSynthesis[2];
		
		   String[] parentAssertions = this.getExtraAssertions();
		   
		   if (parentAssertions == null)
			   parentAssertions = new String[0];
		   
		   String[] lhsAssertions = new String[parentAssertions.length+1];
		   String[] rhsAssertions = new String[parentAssertions.length+1];
		   for (int i = 0; i < parentAssertions.length;i++) {
			   lhsAssertions[i] = parentAssertions[i];
			   rhsAssertions[i] = parentAssertions[i];
		   }
		   lhsAssertions[parentAssertions.length] = pred;
		   rhsAssertions[parentAssertions.length] = "(not " + pred + ")";
		   
		   childJobs[0] = new SplitAndConquerProgramSynthesis(lhsAssertions, 1,this.restarts);
		   childJobs[1] = new SplitAndConquerProgramSynthesis(rhsAssertions, 0,this.restarts);
		   
		
		   return childJobs;
	}

	public String[] getExtraAssertions() {
		return extraAssertions;
	}
	public void setExtraAssertions(String[] extraAssertions) {
		this.extraAssertions = extraAssertions;
	}
	
	public int determineDepth() {
		if (extraAssertions == null) {
			return 1;
		} else {
			return extraAssertions.length + 1;
		}
	}
	
	public int getTiebreaker() {
		return tiebreaker;
	}
	
	public void incrementRestarts() {
		this.restarts++;
	}
	
 
	public int getRestarts() {
		return restarts;
	}
	
	


	@Override
	public int compareTo(SplitAndConquerProgramSynthesis comp) {
		int priorityCheck = 0;
		
		//check depth first, if equal, go to the tiebreaker
		priorityCheck = Integer.compare(comp.determineDepth()+comp.getRestarts(), this.determineDepth()+this.restarts);
		
		if (priorityCheck != 0) {
			return priorityCheck;
		}
		
		//Otherwise, return left most OR, if still present, the root
		return priorityCheck = Integer.compare(comp.getTiebreaker(), this.tiebreaker);
	}



}
