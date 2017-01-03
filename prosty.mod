reset;

##################################################################################################
# DEKLARACJE
##################################################################################################

set SUROWCE;
set PRODUKTY;
set POLPRODUKTY_D;
set POLPRODUKTY_K;
set ILOSC;

param dostepnosc_surowca {s in SUROWCE};
param limity {s in SUROWCE, i in ILOSC};
param cena_surowca_s {s in SUROWCE};
param cena_przetworzenia_surowca {s in SUROWCE, i in ILOSC};
param ilosc_polproduktu_d_na_surowiec {s in SUROWCE, d in POLPRODUKTY_D};
param przygotowalnia_przepustowosc;
param ilosc_polproduktu_k_na_polprodukt_d {d in POLPRODUKTY_D, k in POLPRODUKTY_K};
param uwodornienia_przepustowosc;
param mozliwosc_produkcji_p_z_d {d in POLPRODUKTY_D, p in PRODUKTY};
param mozliwosc_produkcji_p_z_k {k in POLPRODUKTY_K, p in PRODUKTY};
param cena_sprzedazy_produktu_p {p in PRODUKTY};
param cena_pracy_uwodornienia;
param minimalne_zamowienie;
param odniesienia_koszt_produkcji;
param odniesienia_wzgledny_niedobor {p in PRODUKTY};
param max_koszt;

var wykorzystanie_s {s in SUROWCE} integer >= 0;
var wykorzystanie_s_ilosc {s in SUROWCE, i in ILOSC} integer >= 0;
var uzycie_s2 {1..2} binary;
var koszt_wykorzystania_s {s in SUROWCE} integer >= 0;
var wytworzone_polprodukty_d {d in POLPRODUKTY_D} integer >= 0;
var wytworzone_polprodukty_d_na_k {d in POLPRODUKTY_D} integer >= 0;
var wytworzone_polprodukty_d_na_p {d in POLPRODUKTY_D} integer >= 0;
var wytworzone_polprodukty_k {k in POLPRODUKTY_K} integer >= 0;
var wykorzystanie_polproduktu_k_na_p {k in POLPRODUKTY_K, p in PRODUKTY} integer >= 0;
var wykorzystanie_polproduktu_d_na_p {d in POLPRODUKTY_D, p in PRODUKTY} integer >= 0;
var wytworzone_produkty {p in PRODUKTY} integer >= 0;
var koszt_uwodornienia >= 0;
var uwodornienie_pracuje binary;
var koszt >= 0;
var przychod >= 0;

	# metoda punktu odniesienia
var odl_koszt;
var odl_niedobor {p in PRODUKTY};
var odl;
param lambda_koszt;
param lambda_niedobor {p in PRODUKTY};
param epsilon;
param beta;
var v;
var z_niedobor  {p in PRODUKTY};
var z_koszty;

##################################################################################################
# OGRANICZENIA
##################################################################################################

#	###################
# 	dostepnosc surowca s
subject to max_wykorzystanie_s {s in SUROWCE}: dostepnosc_surowca[s] >= wykorzystanie_s[s];

#	###################
# 	podzial wykorzystania surowca w zaleznosci od wykorzystanej ilosci
subject to podzial_surowca {s in SUROWCE}: sum {i in ILOSC} wykorzystanie_s_ilosc[s,i] = wykorzystanie_s[s];

#	###################
# 	warunki podzialu kosztow surowca dla S1
subject to limit1_s1: wykorzystanie_s_ilosc['S1','I1'] <= limity['S1', 'I1'];							# ceny rosna wiec nie
subject to limit2_s1: wykorzystanie_s_ilosc['S1','I2'] <= limity['S1', 'I2'] - limity['S1', 'I1'];	# trzeba wiecej warunkow

#	###################
# 	warunki podzialu kosztow surowca dla S2
subject to limit1_s2: limity['S2', 'I1'] * uzycie_s2[1] <= wykorzystanie_s_ilosc['S2','I1'];
subject to limit2_s2: wykorzystanie_s_ilosc['S2','I1'] <= limity['S2', 'I1'];
subject to limit3_s2: (limity['S2', 'I2'] - limity['S2', 'I1']) * uzycie_s2[2] <= wykorzystanie_s_ilosc['S2','I2'];
subject to limit4_s2: wykorzystanie_s_ilosc['S2','I2'] <= (limity['S2', 'I2'] - limity['S2', 'I1']) * uzycie_s2[1];
subject to limit5_s2: wykorzystanie_s_ilosc['S2','I3'] <= 9999999 * uzycie_s2[2];

#	################### *****
# 	koszt wykorzystania surowca s
subject to ile_kosztuje_wykorzystanie_s {s in SUROWCE}: koszt_wykorzystania_s[s] = 
			wykorzystanie_s[s] * cena_surowca_s[s]
		+	sum {i in ILOSC} (wykorzystanie_s_ilosc[s,i] * cena_przetworzenia_surowca[s, i])
	;

#	###################
# 	ilosc wytworzonych polproduktow d
subject to ile_polproduktow_d {d in POLPRODUKTY_D}: wytworzone_polprodukty_d[d] = sum {s in SUROWCE} (wykorzystanie_s[s] * ilosc_polproduktu_d_na_surowiec[s, d]);

#	###################
# 	wykorzystanie przygotowalni, przerob s na d
subject to max_przygotowalnia_przepust: (sum {s in SUROWCE} wykorzystanie_s[s]) <= przygotowalnia_przepustowosc;

#	################### ?? czy napewno dobry warunek ??
# 	wykorzystanie zakladu uwodornienia, przerob d na k
subject to max_uwodornienia_przepust: (sum {d in POLPRODUKTY_D} wytworzone_polprodukty_d_na_k[d]) <= uwodornienia_przepustowosc;

#	###################
# 	wytworzone_polprodukty_d wykorzystane sa do produkcji k lub p
subject to wszystkie_wytworzone_polprodukty_d {d in POLPRODUKTY_D}: wytworzone_polprodukty_d[d] = wytworzone_polprodukty_d_na_k[d] + wytworzone_polprodukty_d_na_p[d];

#	###################
# 	ilosc wytworzonych polproduktow k
subject to ile_polproduktow_k {k in POLPRODUKTY_K}: wytworzone_polprodukty_k[k] = sum {d in POLPRODUKTY_D} (wytworzone_polprodukty_d_na_k[d] * ilosc_polproduktu_k_na_polprodukt_d[d, k]);

#	###################
# 	wykorzystanie polproduktow k na produkty
subject to jak_wykorzystano_polprodukty_k {k in POLPRODUKTY_K}: (sum {p in PRODUKTY} (wykorzystanie_polproduktu_k_na_p[k,p])) = wytworzone_polprodukty_k[k];

#	###################
# 	wykorzystanie polproduktow d na produkty
subject to jak_wykorzystano_polprodukty_d {d in POLPRODUKTY_D}: (sum {p in PRODUKTY} (wykorzystanie_polproduktu_d_na_p[d,p] * 1)) = wytworzone_polprodukty_d_na_p[d];

#	###################
# 	co z czego można produkowac
subject to produkcja_d_na_p {d in POLPRODUKTY_D, p in PRODUKTY}: wykorzystanie_polproduktu_d_na_p[d,p] <= mozliwosc_produkcji_p_z_d[d,p];
subject to produkcja_k_na_p {k in POLPRODUKTY_K, p in PRODUKTY}: wykorzystanie_polproduktu_k_na_p[k,p] <= mozliwosc_produkcji_p_z_k[k,p];

#	###################
# 	ilosc wytworzonych produktow
subject to ile_produktow_wytworzono {p in PRODUKTY}: wytworzone_produkty[p] = (sum {k in POLPRODUKTY_K} wykorzystanie_polproduktu_k_na_p[k,p]) + (sum {d in POLPRODUKTY_D} wykorzystanie_polproduktu_d_na_p[d,p]);

#	###################
# 	jaki przychod z wytworzonych produktow
subject to licz_przychod: przychod = sum {p in PRODUKTY} wytworzone_produkty[p] * cena_sprzedazy_produktu_p[p];

#	###################
# 	wyliczenie kosztu uwodornienia
subject to licz_koszt_uwodornienia: koszt_uwodornienia >= cena_pracy_uwodornienia * uwodornienie_pracuje;
subject to kiedy_uwodornienie_pracuje: 9999999 * uwodornienie_pracuje >= (sum {d in POLPRODUKTY_D}
wytworzone_polprodukty_d_na_k[d]); 

#	###################
# 	jakie koszta calkowite
subject to licz_koszt_calkowity: koszt = 
		(sum {s in SUROWCE} koszt_wykorzystania_s[s]) 		# koszt zakupy surowca ( + cena koszt przerobu *)
	+	koszt_uwodornienia 									# koszt pracy zakladu uwodornienia
	#+ cena_pracy_uwodornienia
;

#	###################
#	WYLACZONE
# 	minimalnie trzeba tyle wyprodukowac (uwaga to potem bedzie kryterium a nie ograniczenie)
#subject to minm_zamowienie {p in PRODUKTY}: wytworzone_produkty[p] >= minimalne_zamowienie;

#	###################
# 	odleglosci od pkt aspiracji
subject to licz_odl_koszt: odl_koszt = koszt - odniesienia_koszt_produkcji;
subject to licz_odl_niedobor {p in PRODUKTY}: odl_niedobor[p] = 
	(minimalne_zamowienie - wytworzone_produkty[p])/minimalne_zamowienie - odniesienia_wzgledny_niedobor[p];

#	###################
# 	model do pkt odniesienia
subject to licz_odl: odl = v + epsilon * ((sum {p in PRODUKTY} z_niedobor[p]) + z_koszty);
subject to ogr_v_przez_z_koszty: v <= z_koszty;
subject to ogr_v_przez_z_niedobory {p in PRODUKTY}: v <= z_niedobor[p];
subject to ogr_z_przez_koszty_z_krokiem: z_koszty <= beta * lambda_koszt * (koszt - odniesienia_koszt_produkcji);
subject to ogr_z_przez_niedobor_z_krokiem {p in PRODUKTY}: z_niedobor[p] <= beta * lambda_niedobor[p] * odl_niedobor[p];
subject to ogr_z_przez_koszty: z_koszty <= lambda_koszt * (koszt - odniesienia_koszt_produkcji);
subject to ogr_z_przez_niedobor {p in PRODUKTY}: z_niedobor[p] <= lambda_niedobor[p] * odl_niedobor[p];

maximize f_celu: odl;

##################################################################################################
# DODATKOWA FUNKCJA CELU
##################################################################################################

#maximize max_koszt: koszt;

##################################################################################################
# FUNKCJA CELU
##################################################################################################

var zysk;
subject to licz_zysk: zysk = przychod - koszt;
#maximize total_zysk: przychod - koszt;

##################################################################################################
# KONFIGIURACJA
##################################################################################################

data prosty.dat;
option solver cplex;
solve;

display koszt_wykorzystania_s;
display wykorzystanie_s;
display wykorzystanie_s_ilosc;
display wytworzone_polprodukty_d;
display wytworzone_polprodukty_d_na_k;
display wytworzone_polprodukty_d_na_p;
display wytworzone_polprodukty_k;
display wykorzystanie_polproduktu_k_na_p;
display wykorzystanie_polproduktu_d_na_p;
display wytworzone_produkty;
display zysk;
display przychod;
display koszt;
display koszt_uwodornienia;
#display total_zysk;
#display max_koszt;
display odl_koszt;
display odl_niedobor;
display odl;
##################################################################################################