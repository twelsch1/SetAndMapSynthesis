package fitness;

import java.util.ArrayList;

import bcs.verification.CounterExample;
import ec.gp.koza.KozaFitness;

public class VerifiableFitness extends KozaFitness {

	private static final long serialVersionUID = 1111476393375127150L;
	
	private boolean verified = false;
	
	
	//for programs that satisfy all found counterexamples, we run the verification check in evaluate.
	//if it fails, we store the returned counterExample so we don't have to run verification calls again.
	private CounterExample counterExample = null;
	
	private ArrayList<CounterExample> foundCounterExamples = null;
	
	private ArrayList<Float> MADs;
	private ArrayList<Float> testErrors;

	private float negativeSum;
	private float positiveSum;
	
	@Override
	public boolean isIdealFitness() {
		return verified;
	}

	public void setVerified(boolean verified) {
		this.verified = verified;
	}

	public CounterExample getCounterExample() {
		return counterExample;
	}

	public void setCounterExample(CounterExample counterExample) {
		this.counterExample = counterExample;
	}

	public ArrayList<Float> getMADs() {
		return MADs;
	}

	public void setMADs(ArrayList<Float> MADs) {
		this.MADs = MADs;
	}

	public ArrayList<Float> getTestErrors() {
		return testErrors;
	}

	public void setTestErrors(ArrayList<Float> testErrors) {
		this.testErrors = testErrors;
	}

	public float getNegativeSum() {
		return negativeSum;
	}

	public void setNegativeSum(float negativeSum) {
		this.negativeSum = negativeSum;
	}

	public float getPositiveSum() {
		return positiveSum;
	}

	public void setPositiveSum(float positiveSum) {
		this.positiveSum = positiveSum;
	}

	public ArrayList<CounterExample> getFoundCounterExamples() {
		return foundCounterExamples;
	}

	public void setFoundCounterExamples(ArrayList<CounterExample> foundCounterExamples) {
		this.foundCounterExamples = foundCounterExamples;
	}

	
	
	
	
	
	
	
	

}
