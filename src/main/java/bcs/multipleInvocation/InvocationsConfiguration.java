package bcs.multipleInvocation;

import java.util.ArrayList;

public class InvocationsConfiguration {

	private String mainProgram;
	private ArrayList<ArrayList<String>> eqInvocations;
	private ArrayList<ArrayList<String>> distInvocations;
	private ArrayList<ArrayList<String>> replacementInvocations = new ArrayList<>();
	private ArrayList<String> replacementPrograms = new ArrayList<>();
	
	
	/*public InvocationsConfiguration(ArrayList<ArrayList<String>> eqInvocations,
			ArrayList<ArrayList<String>> distInvocations, ArrayList<String> distinctPrograms) {
		this.eqInvocations = eqInvocations;
		this.distInvocations = distInvocations;
		this.distinctPrograms = distinctPrograms;
	}*/
	
	public InvocationsConfiguration(ArrayList<ArrayList<String>> eqInvocations,
			ArrayList<ArrayList<String>> distInvocations) {
		this.eqInvocations = eqInvocations;
		this.distInvocations = distInvocations;
		
		
	}
	
	public InvocationsConfiguration(String mainProgram, ArrayList<ArrayList<String>> eqInvocations,
			ArrayList<ArrayList<String>> distInvocations) {
		this.mainProgram = mainProgram;
		this.eqInvocations = eqInvocations;
		this.distInvocations = distInvocations;
	}
	
	
	
	
	public String getMainProgram() {
		return mainProgram;
	}

	public void setMainProgram(String mainProgram) {
		this.mainProgram = mainProgram;
	}

	public ArrayList<ArrayList<String>> getEqInvocations() {
		return eqInvocations;
	}
	public ArrayList<ArrayList<String>> getDistInvocations() {
		return distInvocations;
	}

	
	
	public ArrayList<ArrayList<String>> getReplacementInvocations() {
		return replacementInvocations;
	}

	public void setReplacementInvocations(ArrayList<ArrayList<String>> replacementInvocations) {
		this.replacementInvocations = replacementInvocations;
	}

	public ArrayList<String> getReplacementPrograms() {
		return replacementPrograms;
	}

	public void setReplacementPrograms(ArrayList<String> replacementPrograms) {
		this.replacementPrograms = replacementPrograms;
	}

	public ArrayList<String> removeFirstDistinctInvocation() {
		return distInvocations.remove(0);
	}
	public void addToEqInvocations(ArrayList<String> invocation) {
		//distInvocations.remove(invocation);
		eqInvocations.add(invocation);
	}
	public void addReplacementInvocation(ArrayList<String> inv) {
		replacementInvocations.add(inv);
	}
	public void addReplacementProgram(String program) {
		replacementPrograms.add(program);
	}
	
	public void removeLastReplacementProgram() {
		////System.out.println("Removing, size before was " + replacementPrograms.size());
		replacementPrograms.remove(replacementPrograms.size()-1);
		////System.out.println("Size after is " + replacementPrograms.size());
	}
	
	public boolean isDistInvocationsEmpty() {
		return distInvocations.isEmpty();
	}
	
	
	
	
	
	
	
	
	
	
}
