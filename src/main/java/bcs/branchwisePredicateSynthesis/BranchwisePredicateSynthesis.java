package bcs.branchwisePredicateSynthesis;

import java.util.ArrayList;
import java.util.HashSet;

import com.microsoft.z3.Status;

import bcs.branchwisePredicateSynthesis.helpers.ExtractPositiveMappings;
import bcs.branchwisePredicateSynthesis.helpers.Reduction;
import bcs.synthesizer.SynthesisResult;
import bcs.synthesizer.Synthesizer;
import bcs.verification.VerificationException;
import bcs.verification.VerificationResult;
import bcs.verification.Verifier;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class BranchwisePredicateSynthesis implements Comparable<BranchwisePredicateSynthesis> {

	/**
	 * The partial for which the mapping is being synthesized.
	 */
	private String targetPartial;
	/**
	 * Partials in the BSPR process that have not yet synthesized mappings.
	 */
	private ArrayList<String> remainingTerms;

	/**
	 * The predicate which restricts the input space during repair process, covers
	 * the inputs where ties need to be resolved.
	 */
	private String repairConstraint;

	/**
	 * Determines if distinctness requirement is enforced.
	 */
	private boolean omitDistinctness = false;

	private int completeMappingsFound = 0;

	private int restrictionsCap = 10;

	private ArrayList<String> restrictions = new ArrayList<>();
	private ArrayList<String> positiveMappings = new ArrayList<>();

	/**
	 * Set to true when we have a correct mapping to targetPartial.
	 */
	private boolean synthesisFinished = false;

	private String correctMapping = "";

	private ArrayList<String> clauses = new ArrayList<>();

	private int numRuns = 0;

	public BranchwisePredicateSynthesis(String partial) {
		this.targetPartial = partial;
		restrictions.add("true");

	}
	
	public void run(Verifier verifier, Synthesizer predicateSynthesizer, boolean verifySuccess,
			int completeMappingsFound, String branchwiseMode) throws Exception {
		
		if (branchwiseMode.equals("RBPS")) {
			runRBPS(verifier, predicateSynthesizer, verifySuccess, completeMappingsFound);
		} else {
			runCBPS(verifier, predicateSynthesizer, verifySuccess, completeMappingsFound);
		}
		
	}
	
	public void runRBPS(Verifier verifier, Synthesizer predicateSynthesizer, boolean verifySuccess,
			int completeMappingsFound) throws Exception {

		setUpVerifier(verifier);

		numRuns++;

		/*If the number of Complete Mappings found in BCS has changed we prune
		PositiveMappings to ensure every element is still a Positive Mapping given the new restrictions.
		We also reset restrictions, after extracting positive mappings, so as to get new restrictions 
		more suited to the search for a Complete Mapping.
		*/
		
		if (this.completeMappingsFound != completeMappingsFound) {

			prunePositiveMappings(verifier);
			for (String r : restrictions) {
				extractPositiveMappingsThenAddToSet(verifier, r);
			}
			resetRestrictions();
		}
		this.completeMappingsFound = completeMappingsFound;

		//This way we don't remove the true value, I wonder if that was messing with things...
		if (restrictions.size() > restrictionsCap) {
			extractPositiveMappingsThenAddToSet(verifier, restrictions.get(1));
			restrictions.remove(1);
		}

		do {
			while (!restrictions.isEmpty()) {
				String[] localRestrictions = buildLocalRestrictions();
				
				//Note in the clauses are presented as being included in localRestrictions directly. Programatically
				//this is not the case, but the outcome is logically equivalent.
				if (!clauses.isEmpty()) {
					verifier.setClauses(clauses.toArray(new String[clauses.size()]));
				}
				verifier.setLocalRestrictions(localRestrictions);
				// if with the local restrictions true is a complete mapping, just remove last
				// restriction rather than running another round of synthesis. This was omitted from the
				//first draft of our paper on BCS to make the algorithm more readable but may be included in the next.
				if (verifier.isCompleteMapping("true")) {
					extractPositiveMappingsThenAddToSet(verifier, restrictions.get(restrictions.size()-1));
					restrictions.remove(restrictions.size() - 1);
				} else {

					// Run synthesis with latest Restrictions+PositiveMappings

					SynthesisResult sr = predicateSynthesizer.synthesize(verifier);

					if (sr.isSuccessful()) {

						// Verify that synthesis actually was successful if required
						if (verifySuccess) {
							VerificationResult vr = verifier.verify(sr.getProgramFound());
							if (vr.getStatus() != Status.UNSATISFIABLE) {
								throw new Exception(
										"Synthesizer returned successful SynthesisResult when programFound is incorrect");
							}
						}
						
						// reduce and add to positive mappings, then remove last restriction
						String reducedPred = Reduction.reduceToClausalPositiveMapping(verifier, sr.getProgramFound(),
								buildLocalRestrictions());
						positiveMappings.add(reducedPred);
						extractPositiveMappingsThenAddToSet(verifier, restrictions.get(restrictions.size()-1));
						restrictions.remove(restrictions.size() - 1);
					} else {
						// add the most recently synthesized predicate to restrictions, then
						// check that we still have reachability. If unreachable, and the state
						// of the job is unchanged from the previous loop. Note the paper describes this slightly
						//differently i.e. there it was never added but rather checked beforehand. This change
						//is logically equivalent and is slightly cleaner in the context of the Verifier
						//treating the restrictions as an array.
						restrictions.add(sr.getProgramFound());
						if (!isReachable(verifier, buildLocalRestrictions())) {
							restrictions.remove(restrictions.size() - 1);
						} 
						
						return;
					}
				}
			}
			// we have built at least one clause successfully, add it to the list of
			// clauses, clear positiveMappings, and reset restrictions.
			clauses.add(buildClause());
			
			numRuns = 0; //reset number of runs back to 0, this makes it so that jobs where clauses have been found
			//are given significant priority.
			
			//reset the job for next loop and clear verifier of local restrictions
			positiveMappings.clear();
			resetRestrictions();
			verifier.setClauses(null);
			verifier.setLocalRestrictions(null);

		} while (!verifier.isCompleteMapping(buildCompleteMappingFromClauses()));

		// we have found a CompleteMapping, we set this as correctMapping and signal success.
		correctMapping = buildCompleteMappingFromClauses();
		this.synthesisFinished = true;
		
	}
		
	public void runCBPS(Verifier verifier, Synthesizer predicateSynthesizer, boolean verifySuccess,
			int completeMappingsFound) throws Exception {


		setUpVerifier(verifier);
		numRuns++;

		if (this.completeMappingsFound != completeMappingsFound) {
			prunePositiveMappings(verifier);
		}
		
		this.completeMappingsFound = completeMappingsFound;



		String[] localRestrictions = buildLocalRestrictions();
		verifier.setLocalRestrictions(localRestrictions);

		SynthesisResult sr = predicateSynthesizer.synthesize(verifier);

		if (sr.isSuccessful()) {

			// Verify that synthesis actually was successful if required
			if (verifySuccess) {
				VerificationResult vr = verifier.verify(sr.getProgramFound());
				if (vr.getStatus() != Status.UNSATISFIABLE) {
					throw new Exception(
							"Synthesizer returned successful SynthesisResult when programFound is incorrect");
				}
			}

			positiveMappings.add(sr.getProgramFound());
			clauses.add(buildClause());

			correctMapping = buildCompleteMappingFromClauses();
			this.synthesisFinished = true;
		} else {
			this.extractPositiveMappingsThenAddToSet(verifier, sr.getProgramFound());
			return;
		}

	}
	
	public void setUpVerifier(Verifier verifier) {
		if (!remainingTerms.isEmpty()) {
			verifier.setRemainingPartials(remainingTerms.toArray(new String[remainingTerms.size()]));
		}

		if (repairConstraint != null) {
			verifier.setRepairConstraint(repairConstraint);
		}
		verifier.setOmitDistinctness(omitDistinctness);
		verifier.setTargetPartial(this.getTargetPartial());
	}

	private String buildCompleteMappingFromClauses() {
		String retVal = "";
		if (clauses.size() == 1) {
			retVal = clauses.get(0);
		} else {
			//System.out.println("Multiple clauses were needed");
			String closingParens = "";
			for (int i = 0; i < clauses.size() - 1; i++) {
				String clause = clauses.get(i);
				retVal += "(or " + clause + " ";
				closingParens += ")";
			}
			retVal += clauses.get(clauses.size() - 1) + closingParens;
		}

		return retVal;
	}	

	private String buildClause() {
		String retVal = "";

		if (positiveMappings.size() == 1) {
			retVal = positiveMappings.get(0);
		} else {

			String closingParens = "";
			for (int i = 0; i < positiveMappings.size() - 1; i++) {
				String pm = positiveMappings.get(i);
				retVal += "(and " + pm + " ";
				closingParens += ")";
			}
			retVal += positiveMappings.get(positiveMappings.size() - 1) + closingParens;
		}

		return retVal;
	}

	private String[] buildLocalRestrictions() {
		ArrayList<String> extraAssertions = new ArrayList<>();
		extraAssertions.addAll(restrictions);
		extraAssertions.addAll(positiveMappings);
		return extraAssertions.toArray(new String[extraAssertions.size()]);
	}

	private void resetRestrictions() {
		restrictions.clear();
		restrictions.add("true");
	}

	public void extractPositiveMappingsThenAddToSet(Verifier verifier, String predicate) {
		HashSet<String> pm = ExtractPositiveMappings.extractPositiveMappings(verifier, predicate);
		for (String s : pm) {
			if (!positiveMappings.contains(s)) {
				positiveMappings.add(s);
			}
		}
	}
	
	public void prunePositiveMappings(Verifier verifier) {
		ArrayList<String> newPartialMappings = new ArrayList<>();
		for (String pm : positiveMappings) {
			if (verifier.isPositiveMapping(pm, null)) {
				newPartialMappings.add(pm);
			} 
		}

		positiveMappings.clear();
		positiveMappings.addAll(newPartialMappings);
	}	
	
	private boolean isReachable(Verifier verifier, String[] extraAssertions) throws VerificationException {
		return !verifier.isCompleteMapping("false");
	}

	public String getCorrectMapping() {
		return correctMapping;
	}

	public boolean isSynthesisFinished() {
		return synthesisFinished;
	}


	public String getTargetPartial() {
		return targetPartial;
	}

	public int getNumRuns() {
		return numRuns;
	}
	
	public void setRemainingTerms(ArrayList<String> remainingTerms) {
		this.remainingTerms = remainingTerms;
	}
	
	public void setRepairConstraint(String repairConstraint) {
		this.repairConstraint = repairConstraint;
	}

	public void setOmitDistinctness(boolean omitDistinctness) {
		this.omitDistinctness = omitDistinctness;
	}


	
	@Override
	public int compareTo(BranchwisePredicateSynthesis comp) {

		// prioritize the one with fewer runs i.e. to make sure every job gets a turn.
		return Integer.compare(this.getNumRuns(), comp.getNumRuns());

	}
	

}
