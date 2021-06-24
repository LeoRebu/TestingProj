
import java.util.ArrayList; 


/*
 * Piccola classe utilizzata per salvare i dati importati dal file generato dal programma cpp
 * Contiene informazioni relative all'alveare ed una lista di "reports"
 * i reports sono snapshots riguardanti lo stato della colonia in un momento del tempo (definiti nella classe Report)
 */
public class Colonia {

	private /*@ spec_public*/ String name;	// Nome identificativo colonia
	private /*@ spec_public*/ int yobQueen;	// Anno di nascita regina (es 2020)
	private /*@ spec_public*/ int qualityQueen; // Indice qualitativo tra 1-5
	private /*@ spec_public*/ int totHoney;	// Valore cumulativo miele prodotto negli anni
	private /*@ spec_public*/ /*@ non_null*/ ArrayList<Report> reportList;	// Lista contenente tutti i report
	
	//@ public invariant totHoney >= 0;

	/*
	 * Costruttore senza parametri
	 */
	//@ ensures yobQueen == 2015;
	//@ ensures qualityQueen == 1;
	//@ ensures totHoney == 0;
	//@ ensures reportList != null;
	public Colonia() {
		name="";
		yobQueen=2015;
		qualityQueen=1; 
		totHoney=0;
		reportList = new ArrayList<Report>();
	}

	/*
	 * Costruttore con parametri
	 */
	//@ requires yq > 2014;
	//@ requires qq > 0 && qq <6;
	//@ requires th >= 0;
	//@ requires rl != null;
	//@ ensures name == n;
	//@ ensures yobQueen == yq;
	//@ ensures qualityQueen == qq;
	//@ ensures totHoney == th;
	//@ ensures reportList == rl;
	//@ ensures (\forall int i; i >= 0 && i < rl.size(); rl.get(i) != null);
	public Colonia(String n, int yq, int qq, int th, ArrayList<Report> rl) {
		name=n;
		yobQueen=yq;
		qualityQueen=qq;
		totHoney=th;
		reportList = rl;
	}
	
	/*
	 * Metodi set
	 */
	
	//@ ensures name == n;
	public void setName(String n) {
		name = n;		
	}
	
	//@ requires yq > 2014;
	//@ ensures yobQueen == yq;
	public void setYobQueen(int yq) {
		if (yq>2014)
			yobQueen = yq;		
	}
	
	//@ requires qq > 0;
	//@ requires qq < 6;
	//@ ensures qualityQueen == qq;
	public void setQualQueen(int qq) {
		if (qq>0 && qq<6)
			qualityQueen = qq;		
	}
	
	//@ requires th >= 0;
	//@ ensures totHoney == \old(totHoney) + th;
	public void increaseTotalHoney(int th) {
		if (th>0) {
			assert th >= 0 : " Valore negativo";
			totHoney += th;		
		}
	}
	
	//@ requires report != null;
	//@ ensures reportList.get(reportList.size()-1) == report;
	public void addReport(Report report) {
		assert report != null : " Report non inizializzato";
		reportList.add(report);	
		
		
	}
	
	/*
	 * Metodi get
	 */
	
	//@ ensures \result == name;
	public String getName() {
		return name;
	}
	//@ ensures \result == yobQueen;
	public int getYobQueen() {
		return yobQueen;
	}
	//@ ensures \result == qualityQueen;
	public int getQualQueen() {
		return qualityQueen;
	}
	//@ ensures \result == totHoney;
	public int getTotalHoney() {
		return totHoney;
	}
	//@ ensures \result == reportList;
	public ArrayList<Report> getReports() {
		assert reportList != null : " Lista report non inizializzata";
		return reportList;
	}
}
