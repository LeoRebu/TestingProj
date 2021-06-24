import java.util.Calendar;
import java.util.Date;
/*
 * Classe per definire i fattori rilevanti dei report e fornire alcuni metodi per la loro interpretazione
 * I metodi forniti sono:
 * 	swarmRisk: 
 * 		Ritorna un valore tra 0 e 5 rappresentante il rischio di sciamatura
 *  starvingRisk:
 *  	Ritorna un valore tra 0 e 5 rappresentante il rischio di denutrimento
 *  needsSuper:
 *  	Ritorna un boolean rappresentante la necessita' di aggiungere un melario
 */
public class Report {
	private /*@ spec_public*/ Date reportDate; // Identificativo report
	private /*@ spec_public*/ int broodFrames; // Numero favi con covata (indicativo di crescita) 
	private /*@ spec_public*/ int honeyFrames; // Numero favi con miele nella cassa (indicativo di richiesta melari)
	private /*@ spec_public*/ int beeFrames;	// Numero favi con api (indicativo di affollamento)
	private /*@ spec_public*/ Boolean seenQueen; // Mancanza della regina 
	private /*@ spec_public*/ Boolean swarmCells; // Presenza cupolino (indicativo di sciamatura)
	private /*@ spec_public*/ int numSupers; // Numero di melari presenti
	private /*@ spec_public*/ float percTopSuper; // Percentuale utilizzo ULTIMO melario (tra 0 ed 1)
	
	//@ public invariant broodFrames >= 0 && broodFrames <= 12;
	//@ public invariant honeyFrames >= 0 && honeyFrames <= 12;
	//@ public invariant beeFrames >= 0 && beeFrames <= 12;
	//@ public invariant numSupers >= 0 && numSupers <= 3;
	//@ public invariant percTopSuper >= 0 && percTopSuper <= 1;
	
	public Report() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);
		reportDate = new Date();
		reportDate = cal.getTime();
		broodFrames=0;
		honeyFrames=0;
		beeFrames=0;
		seenQueen=false;
		swarmCells=false;
		numSupers=0;
		percTopSuper=0;
	}

	//@ requires d != null;
	//@ requires bf >= 0 && bf <= 12;
	//@ requires hf >= 0 && hf <= 12;
	//@ requires bef >= 0 && bef <= 12;
	//@ requires ns >= 0 && ns <= 3;
	//@ requires pts >= 0 && pts <= 1;
	//@ requires ns == 0 ==> pts == 0;
	//@ ensures reportDate == d;
	//@ ensures broodFrames == bf;
	//@ ensures honeyFrames == hf;
	//@ ensures beeFrames == bef;
	//@ ensures seenQueen == sq;
	//@ ensures swarmCells == sc;
	//@ ensures numSupers == ns;
	//@ ensures percTopSuper == pts;
	//@ ensures ns == 0 ==> percTopSuper == 0;
	public Report(Date d, int bf, int hf, int bef, Boolean sq, Boolean sc, int ns, float pts) {
		reportDate = d;
		if (bf>=0 && bf <=12)
			broodFrames=bf;
		else
			broodFrames=0;
		if (hf>=0 && hf <=12)
			honeyFrames=hf;
		else
			honeyFrames=0;
		if (bef>=0 && bef <=12)
			beeFrames=bef;
		else
			beeFrames=0;
		seenQueen=sq;
		swarmCells=sc;
		if (ns>=0 && ns <=3)
			numSupers=ns;
		else
			numSupers=0;
		if (pts>=0 && pts <= 1)
			if (numSupers > 0)
				percTopSuper = pts;
			else
				percTopSuper = 0;
		else
			percTopSuper=0;
	}
	
	//@ requires d != null;
	//@ ensures reportDate == d;
	public void setDate(Date d) {
		if (d!=null)
			reportDate = d;

	}
	
	//@ requires bf >= 0;
	//@ requires bf <= 12;
	//@ ensures broodFrames == bf;
	public void setBroodFrames(int bf) {
		if (bf>=0 && bf <=12)
			broodFrames = bf;
	}
	
	//@ requires hf >= 0;
	//@ requires hf <= 12;
	//@ ensures honeyFrames == hf;
	public void setHoneyFrames(int hf) {
		if (hf>=0 && hf <=12)
			honeyFrames = hf;
	}
	
	//@ requires bef >= 0;
	//@ requires bef <= 12;
	//@ ensures beeFrames == bef;
	public void setBeeFrames(int bef) {
		if (bef>=0 && bef <=12)
			beeFrames = bef;
	}
	
	//@ ensures seenQueen == sq;
	public void setSeenQueen(Boolean sq) {
		seenQueen = sq;
	}
	
	//@ ensures swarmCells == sc;
	public void setSwarmCells(Boolean sc) {
		swarmCells = sc;
	}
	
	//@ requires ns >= 0;
	//@ requires ns <= 3;
	//@ ensures numSupers == ns;
	//@ ensures ns == 0 ==> percTopSuper == 0;
	public void setNumSupers(int ns) {
		if (ns>=0 && ns<=3) {
			numSupers = ns;
			if (ns==0)
				percTopSuper = 0;
		}
	}
	
	//@ requires pts >= 0;
	//@ requires pts <= 1;
	//@ requires numSupers > 0;
	//@ ensures percTopSuper == pts;
	public void setPercTopSuper(float pts) {
		if (numSupers > 0 && pts >= 0 && pts <= 1) 
			percTopSuper = pts;
	}
	
	
	public Date getDate() {
		return reportDate;
	}
	public int getBroodFrames() {
		return broodFrames;
	}
	public int getHoneyFrames() {
		return honeyFrames;
	}
	public int getBeeFrames() {
		return beeFrames;
	}
	public Boolean getSeenQueen() {
		return seenQueen;
	}
	public Boolean getSwarmCells() {
		return swarmCells;
	}
	public int getNumSupers() {
		return numSupers;
	}
	public float getPercTopSuper() {
		return percTopSuper;
	}
	
	// Ritorna un valore tra 0 e 5 rappresentante il rischio di sciamatura
	//@ ensures \result >= 0 && \result <= 5;
	public int swarmRisk() {
		int risk = 0;
		if (broodFrames > 9)
			risk++;
		
		if (swarmCells)
			risk+=2;
		
		if (beeFrames > 10 && numSupers==0)
			risk++;
		
		if (honeyFrames > 4)
			if (numSupers == 0) {
				assert honeyFrames > 4 : " Errore nesting ifs";
				risk++;
			}
			else if (percTopSuper >= 0.8) {
				assert honeyFrames > 4 : " Errore nesting ifs";
				assert numSupers > 0 : " Errore melari rischio sciamatura";
				risk++;
			}
				
		assert risk >= 0 && risk <6 : " Errore calcolo rischio";
		return risk;
	}
	
	// Ritorna un valore tra 0 e 5 rappresentante il rischio di denutrimento
	//@ ensures \result >= 0 && \result <= 5;
	public int starvingRisk() {
		int risk = 0;
		if (honeyFrames < 2) {
			risk++;
			if (numSupers == 0) {
				assert honeyFrames < 2 : " Errore nesting ifs";
				risk+=2;
			}
			else {
				assert honeyFrames < 2 : " Errore nesting ifs";
				assert numSupers > 0 : " Melari Negativi";
				if (beeFrames > 9)
					risk++;
				if (broodFrames > 10)
					risk+=2;
			}
			if(honeyFrames == 0) 
				risk++;
		}

		assert risk >= 0 && risk <6 : " Errore calcolo rischio";
		return risk;
	}
	
	//Ritorna un boolean rappresentante la necessita' di aggiungere un melario
	
	//@ requires honeyFrames > 3;
	//@ ensures \result == true || \result == false;
	public Boolean needsSuper() {
		if ( honeyFrames > 3)
			if (numSupers == 0) {
				assert honeyFrames > 3 : " Errore nesting ifs";
				return true;
			}
			else if (numSupers < 3 && percTopSuper >= 0.8) {
				assert numSupers>0 && numSupers<3 && percTopSuper>=0.8 : " Errore necessita' melari";
				return true;
			}
		
		return false;
	}
}
