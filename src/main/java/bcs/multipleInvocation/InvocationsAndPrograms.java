package bcs.multipleInvocation;

import java.util.ArrayList;

public class InvocationsAndPrograms {

	private ArrayList<ArrayList<String>> invocations;
	private ArrayList<String> programs;
	
	
	public InvocationsAndPrograms(ArrayList<ArrayList<String>> invocations, ArrayList<String> programs) {
		this.invocations = invocations;
		this.programs = programs;
	}
	
	public ArrayList<ArrayList<String>> getInvocations() {
		return invocations;
	}
	public ArrayList<String> getPrograms() {
		return programs;
	}
	
	
	
	
}
