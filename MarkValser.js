/*jshint maxcomplexity:50 */
/*global module, define */
/*Version V 1.2 - factorisation de code : node_clone*/
/*Version V 1.3 - validation IE < Edge : function.name, new RegExp(nreg, 'gi') --> new RegExp(nreg.source, 'gi') */

var MarkValser = (function () {
    "use strict";
                                      //      RegExp Variables
    var REpar = /\$(\d+)/g,
        REcond = /\{(.*?)\}/g,
        REcondCap = /(\{(.*?)\})/g,
        RExparms = /_(\d+)_/g,
        REprimitiveCapt = /\(([^()]*)\)/g,
        REword = /(\S*)/i,
        REnum = /(\d*)/i,
        REparext = /\$E/g,
        REanything = /(.*)/i,
        REmetacar = /[\!|\^|\$|\(|\)|\[|\]|\{|\}|\?|\+|\*|\.|\/|\\|\|]/g,
        REfunc = /^function\s+([\w\$]+)\s*/,
        REurlStr = /(^(?:(?![^:@]+:[^:@\/]*@)([^:\/?#.]+):)?(?:\/\/)?((?:(([^:@]*)(?::([^:@]*))?)?@)?([^:\/?#]*)(?::(\d*))?)(((\/(?:[^?#](?![^?#\/]*\.[^?#\/.]+(?:[?#]|$)))*\/?)?([^?#\/]*))(?:\?([^#]*))?(?:#(.*))?))/i,

                                      // OUTPUTS :
        rems = [],                    // array of remarks
        arrtBB = [],                  // main structure elaborated with text input
        arrtBBsensitive = [],         // permanent saves of tags witch differ on case sensitive 
        arrtBBanticlosing = [],       // permanent saves of tags witch differ on '\' ( '/') 
        arboBBC = [],                 // main drawer structure
        arboBBC_opening_orphan = [],  // opening tag without closing correspondent
        arboBBC_closing_orphan = [],  // closing tag without opening correspondent
        arboBBC_crossing = [],        // crossing nodes
        textBB_after,                 // BBText output (if possible !)
        textBB_after_BB,              // BBText output (colorized for corrections / optimizations ...)
        output_trad_text,             // Real output (HTML but anything else !)
        stats_maxchain,               // max deep 'ancestry' BBnode;
        last_crossing_ind,            // correspond to the index of arrtBB for the first unrecoverable error !

        closingNbTags = {},           // permanent object for tags with same closing but differents names
        namefunctions,                // permanent array for "filter" function names and "trad" function names

        regle,                        // regle = one line of BBC_Def
        nreg,                         // nreg : opening or closing
        i,                            // itérators
        t,                            // itérators
        h,                            // itérators
        j,                            // itérators
        N,                            // Big array to store textBB_before : one textenode / one node / one textnode / one node / etc ...
        match,                        // temporary storage during a boucle
        tmpmatchs;                    // temporary result (array) of a 'match' 


    function inArray(needle, haystack) {
        var length = haystack.length;
        for (i = 0; i < length; i += 1) {
            if (haystack[i] === needle) { return true; }
        }
        return false;
    }

    // http://www.js-attitude.fr/2012/12/26/convertir-un-nombre-en-texte-en-javascript/
    function cleanInt(j) {
        j = Number(j);
        return Math[j >= 0 ? 'floor' : 'ceil'](j);
    }

    // Structure verification
    function verif_struct(BBC_Def) {
        var lng;
        if (!Array.isArray(BBC_Def)) {
            rems.push('BBC_Def is not an array !');
            return;
        }
        lng = BBC_Def.length;
        for (i = 0; i < lng; i += 1) {
            if ((BBC_Def[i].name === undefined) || (BBC_Def[i].absorbent === undefined) || (BBC_Def[i].mother === undefined) || 
                (BBC_Def[i].daugthers === undefined) || (BBC_Def[i].auto === undefined) || (BBC_Def[i].opening === undefined) || 
                (BBC_Def[i].closing === undefined) || (BBC_Def[i].paramint === undefined)  || (BBC_Def[i].paramext === undefined) || 
                (BBC_Def[i].trad === undefined)) {
                rems.push('BBC_Def[' + i.toString() + '] is uncomplete !');
                return;
            }
        }
    }

    // Creation of canonic forms for openings and closings ( regle.CanonicOpening et regle.CanonicClosing)
    function canonic_forms_creation(BBC_Def) {
        var Canonic;
        var lng = BBC_Def.length;
        for (t = 0; t < lng; t += 1) {
            regle = BBC_Def[t];
            nreg = regle.opening[0];
            Canonic = regle.opening[0].split('_'); 
            regle.CanonicOpening = Canonic.join(''); 
            Canonic = regle.closing[0].split('_');
            regle.CanonicClosing = Canonic.join('');
        }
    }

    // Verification of any character to be 'escaped' in Canonic forms
    function any_charater_to_be_escaped(BBC_Def) {
        var meta,
            params,
            conds,
            lng,
            parNb = 0,
            condNb = 0,
            metaNb = 0;
        lng = BBC_Def.length;
        for (h = 0; h < lng; h += 1) {
            meta = BBC_Def[h].CanonicOpening.match(REmetacar);
            params = BBC_Def[h].CanonicOpening.match(REpar);
            if (params !== null) { parNb = params.length; }
            conds = BBC_Def[h].CanonicOpening.match(REcond);
            if (conds !== null) { condNb = conds.length; }
            if (meta.length - parNb - (2 * condNb) > 2) {
                rems.push('BEWARE : ' + BBC_Def[h].name + " contains one or several metacharactere(s) in opening definition !");
            }
            meta = BBC_Def[h].CanonicClosing.match(REmetacar);
            if (meta !== null) { metaNb = meta.length; }
            if (metaNb > 3) {
                rems.push('BEWARE : ' + BBC_Def[h].name + " contains one or several metacharactere(s) in closing definition !");
            }
        }
    }

    //  verification absorbent tag must have a closing tag
    function verification_closing_for_absorbent(BBC_Def) {
        var lng = BBC_Def.length;
        for (h = 0; h < lng; h += 1) {
            if (BBC_Def[h].absorbent && (BBC_Def[h].closing[0] === '')) {
                rems.push('BEWARE : ' + BBC_Def[h].name + " is absorbent BUT have not a closing tag !");
            }
        }
    }

    // closingNbTags is to avoid creation of no-useless "nodes" if 2 (or more) tag(s) have the same closing !
    function closingNbTags_creation(BBC_Def) {
        var BBC_tags = [],                     // temporary Array 
            closingT,                          // temporary Canonic form
            lng;  
        lng = BBC_Def.length;                            
        for (h = 0; h < lng; h += 1) {
            closingT = BBC_Def[h].CanonicClosing;
            if (!inArray(closingT, BBC_tags)) {
                BBC_tags.push(BBC_Def[h].CanonicClosing);
                closingNbTags[closingT] = [h];
            } else {
                if (!inArray(BBC_Def[h].CanonicClosing, closingNbTags)) {
                    closingNbTags[closingT].push(h);
                }
            }
        }
    }

    // create params and paramsname in BBC_Def for each line / tag defined
    // and verify count of paramints
    // Same number of paramints (in definition) as number of parameters called in opening
    function verification_params_defined_and_params_called(BBC_Def) {
        var params,
            lng,
            paramsname;
        lng = BBC_Def.length;    
        for (t = 0; t < lng; t += 1) {
            regle = BBC_Def[t];
            nreg = regle.opening[0];
            params = [];
            paramsname = [];
            while ((match = REpar.exec(nreg)) !== null) {
                paramsname.push(match[0]);
                if (!inArray(match[0], params)) {
                    params.push(match[0]);
                }
            }
            if (params.length !== regle.paramint.length) {
                rems.push('BEWARE - Number of paramints (' + regle.paramint.length.toString() + ') does not equal to number of called parameters (' + params.length.toString() + ') in opening of ' + regle.name + " !");
            } else {
                regle.params = params;
                regle.paramsname = paramsname;
            }
        }
    }

    // Verifications there is no condition without parameters !
    function verification_nbconditions_vs_nbparameters(BBC_Def) {
        var matchcond,   
            lng,
            tmpmatches;
        lng = BBC_Def.length;    
        for (t = 0; t < lng; t += 1) {
            nreg = BBC_Def[t].opening[0];
            j = 1;
            while ((matchcond = REcond.exec(nreg)) !== null) {
                tmpmatches = matchcond[0].match(REpar);
                if (tmpmatches === null) {
                    rems.push('BEWARE - The condition number ' + j.toString() + " of " + BBC_Def[t].opening + " does not contain any parameter !");
                }
            }
            j += 1;
        }
    }

    // verification existence of fonctions "trad" and "filter"
    function verification_functions(BBC_Def, afunctions) {
        var filter,
            match,
            lng;        
        // initialization of namefunctions witch is global !
        // Be careful : function.name isn't known for IE < Edge (or 12)
        namefunctions = [];
        lng = afunctions.length;
        for (t = 0; t < lng; t += 1) {
            //console.log(afunctions[t].toString());
            match = REfunc.exec(afunctions[t].toString());
            if (match !== null){
                namefunctions.push(match[1]);    
            }
            /*
            if (afunctions[t].name !== undefined) {
                namefunctions.push(afunctions[t].name);
            }
            */
        }
        lng = BBC_Def.length;        
        for (t = 0; t < lng; t += 1) {
            regle = BBC_Def[t];
            nreg = regle.opening[0];
            for (i = 0; i < regle.paramint.length; i += 1) {
                if (regle.paramint[i] === 'function') {
                    filter = regle.name + "_filter_" + regle.params[i];
                    if (!inArray(filter, namefunctions)) {
                        rems.push(filter + " doesn't exist OR this is not a function !");
                    }
                }
            }
            if (regle.trad === 'function') {
                filter = regle.name + "_trad";
                if (!inArray(filter, namefunctions)) {
                    rems.push(filter + " doesn't exist OR this is not a function !");
                }
            }
        }
    }

    // verifications others (mother daugthers etc)
    function verification_others(BBC_Def){
        var lng,
            namestag = [];
        lng = BBC_Def.length;    
        // verification each tag have an unique name
        for (t = 0; t < lng; t += 1) {
            if (!inArray(BBC_Def[t].name, namestag)) {
                namestag.push(BBC_Def[t].name);
            } else {
                rems.push(BBC_Def[t].name + " seems to be in double ! Each name must be unique.");    
            }
        }
        // verification each mother represents an unique tag
        for (t = 0; t < lng; t += 1) {
            if ((BBC_Def[t].mother !== []) && (BBC_Def[t].mother !== null)){
                for (i=0; i<BBC_Def[t].mother.length; i++){
                    if (!inArray(BBC_Def[t].mother[i], namestag)){
                        rems.push(BBC_Def[t].name + " : there is one undefined mother : " + BBC_Def[t].mother[i]);    
                    }
                }
            }
        }
        // verification each daugther represents an unique tag
        for (t = 0; t < lng; t += 1) {
            if ((BBC_Def[t].daugthers !== []) && (BBC_Def[t].daugthers !== null)){
                for (i=0; i<BBC_Def[t].daugthers.length; i++){
                    if (!inArray(BBC_Def[t].daugthers[i], namestag)){
                        rems.push(BBC_Def[t].name + " : there is one undefined daugther : " + BBC_Def[t].daugthers[i]);    
                    }
                }
            }
        }
    }

    // add regopening, regclosing, tabParHC, tabPar, openingPar, 
    //     openingCond, CanonicOpeningForm, CanonicOpeningConds
    function complete_regles(BBC_Def) {
        var indices_par,
            nregforming,
            param,
            params,
            openingPar,
            openingCond,
            tabPar,
            regopeningStr,
            regopeningStrRef,
            str_repl,
            ecart,
            newTab,
            TabParHC,
            TabParSC,
            tmpind,
            valdeb,
            valfin,
            canonicconds,
            openingRef,
            lng1,
            ncanon;
        lng1 = BBC_Def.length;    
        for (t = 0; t < lng1; t += 1) {
            regle = BBC_Def[t];
            nreg = regle.opening[0];
            params = regle.params;
            if (params !== null) {
                // replace parameter $i by (.*?)
                for (i = 0; i < params.length; i += 1) { 
                    param = new RegExp('\\' + params[i], 'g');
                        nreg = nreg.replace(param, '(.*?)');
                }
            }
            // '-' => (\s*) ... '/' => '\/' ... '[' => '\[' ... ']' => '\]' ... '{' => '('   AND '}' => ')?'
            nreg = nreg.replace(/_/g, '(\\s*)');          // non canonic spaces
            nreg = nreg.replace(/\//g, '\/');             // \ of closing tag  !!      REQUIRED !!
            nreg = nreg.replace(/\[/g, '\\[');            // délimiter tag before
            nreg = nreg.replace(/\]/g, '\\]');            // délimiter tag after
            nreg = nreg.replace(/\{/g, '(');              // condition aperture
            nreg = nreg.replace(/\}/g, ')?');             // condition closure :D
            if (regle.opening[1]) {
                nregforming = new RegExp(nreg, 'gi');
            } else {
                nregforming = new RegExp(nreg, 'g');
            }
            regle.regopening = nregforming;               // we have it ! This is "regexp" of opening[0]

            openingPar = [];
            openingCond = [];
            tabPar = [];
            i = 0;
            regopeningStr = nreg.toString();
            regopeningStrRef = regopeningStr;
            str_repl = '';
            ncanon = [];
            // replace all 'canonics spaces' (\s*) AND params ($0, $1, $2, ...) by _i_
            while ((match = REprimitiveCapt.exec(regopeningStrRef)) !== null) {
                str_repl = '_' + i.toString() + '_';
                regopeningStr = regopeningStr.replace(match[0], str_repl);
                if (match[0] === '(\\s*)') {
                    ncanon.push(i);    // save indices for 'canonics spaces'
                }
                i += 1;
            }
            // i = nb of canonics spaces PLUS params 
            // in regopeningStr the '(' and ')?' are for conditions ONLY now
            // So newTab is array of conditions :
            newTab = regopeningStr.match(REprimitiveCapt);
            indices_par = 0;
            ecart = 1;                // Capture indice 0 is the whole regopening
            TabParHC = [];
            TabParSC = [];
            if (newTab !== null) {    // There is one condition or more
                // for each condition save positions of first and last parameters in newTab
                for (j = 0; j < newTab.length; j += 1) {
                    tmpind = newTab[j].match(RExparms);
                    // valdeb : first position
                    valdeb = cleanInt(tmpind[0].substr(1, tmpind[0].length - 2));
                    // valfin : last position                 
                    valfin = cleanInt(tmpind[tmpind.length - 1].substr(1, tmpind[tmpind.length - 1].length - 2));
                    newTab[j] = [valdeb, valfin];
                }
                // Now, parse all indices which are neither 'canonics spaces' nor 'conditions' (indice_par += 1)
                for (j = 0; j < newTab.length; j += 1) {
                    // indices_par except conditions
                    while (indices_par < newTab[j][0]) {
                        if (!inArray(indices_par, ncanon)) {
                            openingPar.push(indices_par + ecart);
                            TabParHC.push(indices_par + ecart);
                        }
                        indices_par += 1;
                    }
                    // save this indice for condition
                    openingCond.push(indices_par + ecart);
                    ecart += 1;                                // because condition
                    // indices under conditions
                    while (indices_par < newTab[j][1] + 1) {
                        if (!inArray(indices_par,  ncanon)) {
                            openingPar.push(indices_par + ecart);
                            TabParSC.push(indices_par + ecart);
                        }
                        indices_par += 1;
                    }
                    tabPar.push(TabParSC);                     // save TabParSC in tabPar
                    TabParSC = [];                             // and reset
                }
                // after last condition
                while (indices_par < i) {
                    if (!inArray(indices_par, ncanon)) {
                        openingPar.push(indices_par + ecart);
                    }
                    indices_par += 1;
                }
            } else {    // There is no condition
                params = [];
                params = regopeningStr.match(RExparms);

                for (j = 0; j < params.length; j += 1) {
                    if (!inArray(j, ncanon)) {
                        openingPar.push(j + ecart);
                        TabParHC.push(j + ecart);
                    }
                }
            }
            regle.openingPar = openingPar;
            regle.openingCond = openingCond;
            regle.tabPar = tabPar;
            regle.tabParHC = TabParHC;

            canonicconds = [];
            nreg = regle.CanonicOpening;
            openingRef = regle.CanonicOpening;
            j = 0;
            while ((match = REcond.exec(openingRef)) !== null) {
                str_repl = match[1];
                canonicconds.push(str_repl);
                nreg = nreg.replace(match[0], '$C' + j.toString());
                j += 1;
            }
            regle.CanonicOpeningForm = nreg;
            regle.CanonicOpeningConds = canonicconds;

            // Now closing !!
            nreg = regle.closing[0];
            // BEWARE closing[0] !== ''  AND t === first of closingNbTags
            if ((nreg !== '') && (t === closingNbTags[BBC_Def[t].CanonicClosing][0])) {  // Attention à l'existence d'une balise fermante !!
                nreg = nreg.replace(/_/g, '(\\s*)');          // espaces non canoniques
                nreg = nreg.replace(/\//g, '\/');             // fermeture tag  ?? 
                nreg = nreg.replace(/\[/g, '\\[');            // délimiteur avant
                nreg = nreg.replace(/\]/g, '\\]');            // délimiteur arrière (si différent)
                nreg = nreg.replace(/\{/g, '(');              // condition ouverture
                nreg = nreg.replace(/\}/g, ')?');             // condition fermeture
                if (regle.closing[1]) {
                    nregforming = new RegExp(nreg, 'gi');
                } else {
                    nregforming = new RegExp(nreg, 'g');
                }
                regle.regclosing = nregforming;
            } else {
                regle.regclosing = '';
            }
        }
    }

    // Verifications and completude of / for BBC_Def !
    function initiate(BBC_Def, afunctions) {
        rems = [];
        verif_struct(BBC_Def);
        if (rems.length > 0) {
            return rems;
        }
        canonic_forms_creation(BBC_Def);
        any_charater_to_be_escaped(BBC_Def);
        if (rems.length > 0) {
            return rems;
        }
        verification_closing_for_absorbent(BBC_Def);
        if (rems.length > 0) {
            return rems;
        }
        closingNbTags_creation(BBC_Def);
        verification_params_defined_and_params_called(BBC_Def);
        if (rems.length > 0) {
            return rems;
        }
        verification_nbconditions_vs_nbparameters(BBC_Def);
        if (rems.length > 0) {
            return rems;
        }
        verification_functions(BBC_Def, afunctions);
        if (rems.length > 0) {
            return rems;
        }
        verification_others(BBC_Def);
        if (rems.length > 0) {
            return rems;
        }
        complete_regles(BBC_Def);
        rems = null;
        return rems;
    }

    // From BBtext_before and BBC_Def, creation of approching drawer structure 'arrtBB' and some little : arrtBBsensitive & arrtBBanticlosing
    function parse_and_create_arrtBB(BBC_Def, BBtext_before) {
        var stmpmatch,
            tmppos,
            newregi,
            lng1, lng2,
            newregopening;
        rems = [];
        arrtBBsensitive = [];
        arrtBBanticlosing = [];
        arrtBB = [];
        for (t = 0, lng1 = BBC_Def.length; t < lng1; t += 1) {
            regle = BBC_Def[t];
            nreg = regle.regopening;
            tmpmatchs = [];
            tmppos = [];
            while ((match = nreg.exec(BBtext_before)) !== null) {
                match.input = t;
                match.absorbed = false;
                tmpmatchs.push(match);
                tmppos.push(match.index);                                      // save position in BBtext_before
            }
            // save captures (tmpmatchs) in arrtBB structure :
            lng2 =tmpmatchs.length;
            for (i = 0; i < lng2; i += 1) {
                arrtBB.push(tmpmatchs[i]);
            }
            // Capture also those witch are case sensitive and save them in arrtBB AND in arrtBBsensitive
            // FIRST improvement : detect forgotten tags because of case sensitive !!
            if (!nreg[1]) {
                stmpmatch = [];
                //newregopening = new RegExp(nreg, 'gi');
                newregopening = new RegExp(nreg.source, 'gi');
                while ((match = newregopening.exec(BBtext_before)) !== null) {
                    match.input = t;
                    match.absorbed = false;
                    stmpmatch.push(match);
                    if (!inArray(match.index, tmppos)) {
                        arrtBBsensitive.push(match);
                        arrtBB.push(match);
                    }
                }
            }
            // same operation with closing but, this time, try to capture too the '\' rather than '/'
            // save them in arrtBBsensitive AND in arrtBB
            nreg = regle.regclosing;                                           // normal closing
            if (nreg !== '') {
                tmpmatchs = [];
                tmppos = [];
                while ((match = nreg.exec(BBtext_before)) !== null) {
                    match.input = t;
                    match.absorbed = false;
                    tmpmatchs.push(match);
                    tmppos.push(match.index);                                  // save temporary position in BBtext_before
                }
                lng2 =tmpmatchs.length;
                for (i = 0; i < lng2; i += 1) {
                    arrtBB.push(tmpmatchs[i]);
                }

                if (!nreg[1]) {                                                // and closing 'sensitive' !!
                    stmpmatch = [];
                    //newregopening = new RegExp(nreg, 'gi');
                    newregopening = new RegExp(nreg.source, 'gi');
                    while ((match = newregopening.exec(BBtext_before)) !== null) {
                        match.input = t;
                        match.absorbed = false;
                        stmpmatch.push(match);
                        if (!inArray(match.index, tmppos)) {
                            arrtBBsensitive.push(match);
                            arrtBB.push(match);
                        }
                    }
                }

                // save them in  arrtBBanticlosing AND in  arrtBB   &&  try to inverse '/' <=> '\'                                                                             
                var str_regclosing = regle.regclosing.toString().replace('\\\/','\\\\');                                                                         
                //var str_regclosing = regle.regclosing.toString().replace('\\\/','\\\\');
                str_regclosing = str_regclosing.substr(1, str_regclosing.lastIndexOf('/') - 1);
                nreg = new RegExp(str_regclosing,'g');
                tmpmatchs=[];
                tmppos = [];
                while ((match = nreg.exec(BBtext_before)) !== null) {
                    match.input=t;
                    match.absorbed = false;
                    match.old = match[0];
                    match[0] = match[0].replace('\\','\/');
                    tmpmatchs.push(match);  
                    tmppos.push(match.index);                                  // save position in BBtext_before
                }
                lng2 =tmpmatchs.length;
                for (i = 0; i < lng2; i += 1) {
                    arrtBBanticlosing.push(tmpmatchs[i]);
                    arrtBB.push(tmpmatchs[i]);         
                }   

                // save them in arrtBBanticlosing, in arrtBBsensitive AND in arrtBB 
                if (!regle.closing[1]){
                    stmpmatch = [];
                    newregi = new RegExp(str_regclosing, 'gi');
                    while ((match = newregi.exec(BBtext_before)) !== null){
                        match.input=t;
                        match.absorbed = false;
                        match.oldc = match[0];
                        match[0] = match[0].replace('\\','\/');
                        stmpmatch.push(match);    
                        if (!inArray(match.index, tmppos)){
                            arrtBBanticlosing.push(match);                        
                            arrtBBsensitive.push(match); 
                            arrtBB.push(match);                                
                        }
                    }
                }                
            }
        }
    }

    // create array N : textnode / BBnode / textnode / BBnode / ... / BBnode / textnode
    function create_N_arrt(text_in){
        var ind1, ind2, ind3, lng;
        N = [];
        N[0] = text_in.substr(0,arrtBB[0].index);
        for (i = 0, lng = arrtBB.length-1; i < lng; i += 1){
            ind1 = arrtBB[i].index;
            ind2 = arrtBB[i+1].index;
            N.push(text_in.substr(ind1, arrtBB[i][0].length));
            ind3 = ind1 + arrtBB[i][0].length;
            N.push(text_in.substr(ind3, ind2-ind3));
        }
        ind1 = arrtBB[arrtBB.length-1].index;
        ind2 = text_in.length;
        ind3 = ind1 + arrtBB[arrtBB.length-1][0].length;
        N.push(text_in.substr(ind1, arrtBB[arrtBB.length-1][0].length));
        N.push(text_in.substr(ind3, ind2 - ind3));
    }

    // SECOND improvement : cleaning tags with Canonics forms (opening and closing)
    function cleaning_of_arrtBB(BBC_Def) {
        var localcond,
            lng1, lng2,
            outcanonicopening,
            ind_HC,
            str_replace,
            ind_in_cond;
        for (t = 0, lng1 = arrtBB.length; t  < lng1; t += 1) {
            regle = BBC_Def[arrtBB[t].input];
            if ((arrtBB[t][0].substr(1, 1) !== '/') && (arrtBB[t][0].substr(1, 1) !== '\\') && (!arrtBB[t].absorbed)) {
                localcond = '';
                outcanonicopening = regle.CanonicOpeningForm;
                for (j = 0, lng2 = regle.CanonicOpeningConds.length; j < lng2; j += 1) {
                    str_replace = '';
                    if (arrtBB[t][regle.openingCond[j]] !== undefined) {
                        localcond = regle.CanonicOpeningConds[j];
                        ind_in_cond = 0;
                        while ((match = REpar.exec(localcond)) !== null) {
                            localcond = localcond.replace(match[0], arrtBB[t][regle.tabPar[j][ind_in_cond]]);
                            ind_in_cond += 1;
                        }
                        str_replace = localcond;
                    }
                    outcanonicopening = outcanonicopening.replace("$C" + j.toString(), str_replace);
                }
                ind_HC = 0;
                while ((match = REpar.exec(outcanonicopening)) !== null) {
                    outcanonicopening = outcanonicopening.replace(match[0], arrtBB[t][regle.tabParHC[ind_HC]]);
                    ind_HC += 1;
                }
                arrtBB[t].outcanonicopening = outcanonicopening;
                if (outcanonicopening !== arrtBB[t][0]) {
                    arrtBB[t].old = arrtBB[t][0];
                    arrtBB[t][0] = outcanonicopening;
                    rems.push('CANONIC REPLACEMENT - arrtBB[' + t.toString() + '] : <' + arrtBB[t].old + '> is replaced by <' + outcanonicopening + '>');
                }
            } else {                 
                if (!arrtBB[t].absorbed) {                                                            // traite closing
                    localcond = regle.CanonicClosing;
                    if (localcond !== arrtBB[t][0]) {
                        arrtBB[t].old = arrtBB[t][0];
                        arrtBB[t][0] = localcond;
                        rems.push('CANONIC REPLACEMENT - arrtBB[' + t.toString() + '] : <' + arrtBB[t].old + '> is replaced by <' + localcond + '>');
                    }
                }
            }
        }
    }

    // Now, we are ready to build the real drawer structure : arboBBC
    // each node of this structure have 3 caracteristics :
    //     1 - a "mother";
    //     2 - daugthers 
    //     3 - his correspondent node : open tag <=> close tag
    //     4 - his 'ancestry'
    //           creation_of_drawer_structure modify arboBBC_opening_orphan, arboBBC_closing_orphan, arboBBC_crossing, arboBBC, arrtBB (absorbed)

    function creation_of_drawer_structure(BBC_Def, closingNbTags) {
        var absorbent = false,           // indicator : 'false' : we are not under a absorbent BBNode, 'true' : we are under an absobent BBNode  
            ind_arrt_abs,                // indice of absobant BBNode
            chainemeres = [-2],          // -2 <=> root of structure ; this is OldMammy ! 
            OMfilles = [],               // array <=> daughters of OldMammy
            indi,                        // current indice
            indk,                        // indice for searching correspondent opening BBNode
            mere,                        // indice of "mother" BBNode
            isbreak,                     // indicator : if ERROR encountered then isbreak is TRUE and we escaped :-(
            lng1, lng2,                  // for "for" boucles 
            tmpchaine;                   // temporary copy of chainemeres
            
        arboBBC_opening_orphan = [];     // opening BBNode without correspondent
        arboBBC_closing_orphan = [];     // closing BBNode without correspondent
        arboBBC_crossing = [];           // for storage pair of opening/closing witch are crossing with other(s) pair(s)
        arboBBC = [];                    // THE drawer STRUCTURE

        isbreak = false;
        lng1 = arrtBB.length;
        for (indi = 0; indi < lng1; indi += 1) {
            // if tag != closing tag, it's a new dawn for us ! So we create another drawer. 
            if (arrtBB[indi][0].substr(1, 1) !== '/') {
                if (!absorbent) {                                          // we are not under an absorbent tag : absorbent indicator is OFF
                    mere = chainemeres[chainemeres.length - 1];
                    if (mere === -2) {                                     // the "mother" is the root of structure
                        OMfilles.push(indi);
                    } else {
                        arboBBC[mere][1].push(indi);                       // so the "mother" have a new daughter :)                         
                    }
                    chainemeres.push(indi);                                // ancestry of current tag 
                    tmpchaine=[];
                    for (i=0, lng2 = chainemeres.length; i < lng2; i++) {
                        tmpchaine.push(chainemeres[i]);
                    }

                    if (BBC_Def[arrtBB[indi].input].closing[0] === '') {   // if no_closing tag, it's an 'autoclosing tag' so
                        arboBBC.push([mere, [], indi, tmpchaine]);         // autoclosed ! the BBNode is his correspondent
                        chainemeres.pop();
                    } else {
                        arboBBC.push([mere, [], -1, tmpchaine]);           // we don't know - now - witch one is the correspondent. '-1' = unknown
                        if (BBC_Def[arrtBB[indi].input].absorbent) {       // beware : if this node is absorbent, we must turn on absorbent indicator
                            absorbent = true;                              // Now, absorbent indicator is ON
                            ind_arrt_abs = indi;                           // save current indice
                        }
                    }
                } else {                                                   // we are under absordent tag
                    arrtBB[indi].absorbed = true;                          // indicate that this BBnode is absorbed
                    tmpchaine=[];
                    for (i=0, lng2 = arboBBC[ind_arrt_abs][3].length; i < lng2; i++) {
                        tmpchaine.push(arboBBC[ind_arrt_abs][3][i]);
                    }
                    tmpchaine.push(indi);                                  // ancestry = ancestry of BBNode indice ind_arrt_abs + this indice 
                    arboBBC.push([ind_arrt_abs, [], -1, tmpchaine]);
                }

            } else {                                                       // it's a closing tag
                if (!absorbent) {                                          // if we are not under an absorbent tag : absorbent indicator is OFF
                    indk = indi - 1;
                    // SO searching for node with same name tag but without correspondent node (opening tag) OR name different but same closing !!
                    while (((BBC_Def[arrtBB[indk].input].name !== BBC_Def[arrtBB[indi].input].name) && (!inArray(arrtBB[indk].input, closingNbTags[arrtBB[indi][0]]))) || ((BBC_Def[arrtBB[indk].input].name === BBC_Def[arrtBB[indi].input].name) && (arboBBC[indk][2] !== -1))) {
                        if (indk > 0) {
                            indk = indk - 1;
                        } else {                                           // last indk = 0 so indi is a closing BBnode whithout opening BBNode : it's an orphan closing node
                            arboBBC_closing_orphan.push(indi);
                            rems.push("Beware " + arrtBB[indi][0] + " seems to close nothing !");
                            arboBBC.push([-1, [], -1, []]);
                            isbreak = true;
                            break;
                        }
                    }

                    if (!isbreak) {                                        // We have found a correspondent node (indk >= 0)
                        if (arboBBC[indk][2] !== -1) {                     // by caution because "while" is little complexe (sorry)
                            arboBBC_closing_orphan.push(indi);
                            rems.push("ERROR arboBBC for tag " + arrtBB[indi][2] + " : tag number " + indk.toString() + " is seen closed but tag number " + indi.toString() + " seems to close it !");
                        } else {
                            arboBBC[indk][2] = indi;                       // indi is the correspondent BBnode of indk and have - necessary - same mother & same ancestry
                            arboBBC.push([arboBBC[indk][0], [], indk, arboBBC[indk][3]]);
                            if (arboBBC_opening_orphan.length > 0) {       // if indk was an opening orphan BBNode, then [indk, indi] is a crossing pair
                                if (inArray(indk, arboBBC_opening_orphan)) {
                                    arboBBC_crossing.push([indk, indi]);
                                }
                            }
                            // VERIFICATION   are there some 'holes' between indk and indi ? (Regulary, each node is closed !)
                            for (t = indk + 1; t < indi; t += 1) {         // searching BBnode opened but not closed
                                if ((arboBBC[t][2] === -1) && (!arrtBB[t].absorbed)) {
                                    if (!inArray(t, arboBBC_closing_orphan)){
                                        rems.push('Beware : ' + arrtBB[t][0] + ' seems to be unclosed !');
                                        arboBBC_opening_orphan.push(t);    // if not in closing orphan, it must be an opening orphan !
                                    }
                                }
                            }
                            tmpchaine=[];
                            for (i=0, lng2 = arboBBC[indk][3].length-1; i < lng2; i++) {
                                tmpchaine.push(arboBBC[indk][3][i]);
                            }
                            chainemeres = tmpchaine;                       // retrieve the "ancestry" of opening tag / correspondent
                        }                                                                                                                                   
                    } else {
                        isbreak = false;                                   // 
                    }
                } else {                                                   // we are under absorbent tag
                    if (BBC_Def[arrtBB[indi].input].name !== BBC_Def[arrtBB[ind_arrt_abs].input].name) {
                        arrtBB[indi].absorbed = true;                      // but indk is not THE first absorbent tag so this tag is absorbed
                        tmpchaine=[];
                        for (i=0, lng2 = arboBBC[indk][3].length-1; i < lng2; i++) {
                            tmpchaine.push(arboBBC[ind_arrt_abs][3][i]);
                        }
                        tmpchaine.push(indi);    
                        arboBBC.push([ind_arrt_abs, [], -1, tmpchaine]);   // ancestry = ancestry of BBNode indice ind_arrt_abs + this indice 
                    } else {                                               // Yes ! we found the closing correpondent 
                        arboBBC[ind_arrt_abs][2] = indi;                   // corespondent absorbent tag :
                        arboBBC.push([arboBBC[ind_arrt_abs][0], [], ind_arrt_abs, arboBBC[ind_arrt_abs][3]]);
                        absorbent = false;                                 // So we are not, now, under absorbent BBNode !
                        tmpchaine=[];
                        for (i=0, lng2 = arboBBC[indk][3].length-1; i < lng2; i++) {
                            tmpchaine.push(arboBBC[ind_arrt_abs][3][i]);
                        }
                        chainemeres = tmpchaine;                           // and chainemere => ancestry of ind_arrt_abs pop() !
                    }
                }
            }
        }
    }

    // make some verification on arboBBC related on "mothers / daugthers / auto",
    // verify all same param are identical and, then, use 'filter' to compare filtered values and original values !
    // store ones and others in values_before_params and values_after_params under arrtBB.
    function correct_parameters(BBC_Def, afunctions){
        var filter,
            mother_tag,
            lng1, 
            lng2,
            k, x;

        lng1 =  arrtBB.length;   
        for (var i=0; i < lng1; i++){
            // First verify mother and daugthers !
            var def=BBC_Def[arrtBB[i].input];
            var corr = arboBBC[i][2];
            if ((def.mother) && (def.mother.length > 0) && (!arrtBB[i].absorbed)) { 
                var mother = arboBBC[i][3][arboBBC[i][3].length - 2];
                if (mother != -2) {
                    mother_tag = BBC_Def[arrtBB[mother].input].name;
                } else {
                    mother_tag = 'OldMammy';
                }    
                if ((!inArray(mother_tag, def.mother)) || (mother_tag === 'OldMammy')) {
                    rems.push('WARNING - arrtBB[' + i.toString() + '] (' + arrtBB[i][0] + ') have not a good mother : "' + mother_tag + '"');
                }
            }
            if ((def.daugthers) && (def.daugthers.length > 0) && (!arrtBB[i].absorbed)) { 
                lng2 = arboBBC[i][1].length;
                for (k = 0; k < lng2; k++) {
                    var daugther = arboBBC[i][1][k];
                    var daugther_tag = BBC_Def[arrtBB[daugther].input].name;
                    if (!inArray(daugther_tag, def.daugthers)){
                        rems.push('WARNING - arrtBB[' + i.toString() + '] (' + arrtBB[i][0] + ') have not a good daugther : "' + daugther_tag + '"');
                    }
                }
            }
            // then 'auto' ! if auto is false ...
            if ((!def.auto) && (corr > i) && (!arrtBB[i].absorbed)){
                for (k= i+1; k < corr; k++){
                    if ((BBC_Def[arrtBB[k].input].name === def.name) && (!arrtBB[k].absorbed)) {
                        rems.push('WARNING - arrtBB[' + k.toString() + '] (' + arrtBB[k][0] + ") can't be a descendant of him self !");    
                    }
                }
            }
            // then daugthers = null : if daugthers == null corr = i+1 OR all BBNodes are absorbed 
            if ((def.daugthers === null) && (!arrtBB[i].absorbed) && (corr > i)){
                if ((corr !== i+1) && (def.absorbent)){
                    // Verification all 'daugthers' must be absorbed
                    for (k= i+1; k < corr; k++){
                        if (!arrtBB[k].absorbed) {
                            rems.push('WARNING - arrtBB[' + k.toString() + '] (' + arrtBB[k][0] + ") must be absorbed because of [" + def.name + "] !");    
                        }
                    }        
                } else {
                    if (corr !== i+1) {
                        rems.push('WARNING - arrtBB[' + i.toString() + '] (' + arrtBB[i][0] + ") can't have daugther !");     
                    }
                }
            }

            // Now, really, verification of value of paramints (if exist) !
            if ((!arrtBB[i].absorbed) && (def.paramint.length > 0) && (!arrtBB[i].add) && (arrtBB[i][0].substr(1, 1) !== '/')) {     // skip tags added and tag closing !!
                var values_before_params = [];
                lng2 = def.params.length;
                for (var n=0; n < lng2; n += 1) {
                    values_before_params.push(null);
                    var namepar = def.params[n];
                    var first = true;
                    for (var indpar = 0; indpar < def.paramsname.length; indpar += 1){
                        if ((def.paramsname[indpar] === namepar) && (arrtBB[i][def.openingPar[indpar]] !== undefined)){
                            if (first) {
                                values_before_params[values_before_params.length-1] = arrtBB[i][def.openingPar[indpar]];
                                first = false;
                            } else {
                                if (arrtBB[i][def.openingPar[indpar]] !== values_before_params[values_before_params.length-1]){
                                    rems.push('WARNING - arrtBB[' + i.toString() + '] (' + arrtBB[i][0] + ") : each param (" + namepar + ") must have same value (**" + arrtBB[i][def.openingPar[indpar]] + "** is different of **" + values_before_params[values_before_params.length-1] + "**)");
                                }
                            }
                        }
                    }
                }
                arrtBB[i].values_before_params = values_before_params;  // firsts values if exist will be apllicated  
                var values_after_params = [];  
                for (n=0; n < lng2; n += 1) {
                    values_after_params.push(null);
                    if (values_before_params[n] !== null) {
                        switch (def.paramint[n]) {
                        case 'W':
                            values_after_params[values_after_params.length-1]  = values_before_params[n].match(REword)[0];
                            break;
                        case 'D':
                            values_after_params[values_after_params.length-1]  = values_before_params[n].match(REnum)[0];
                            break;
                        case 'U':                            
                            values_after_params[values_after_params.length-1]  = values_before_params[n].match(REurlStr)[0];
                            break;
                        case '*':
                            values_after_params[values_after_params.length-1]  = values_before_params[n].match(REanything)[0];
                            break;
                        case 'function' :
                            filter = def.name + "_filter_" + def.params[n]; //                             
                            x=0;
                            while (filter !== namefunctions[x]) x += 1;
                            values_after_params[values_after_params.length-1] = afunctions[x](values_before_params[n]);     
                        }
                    }   
                    if (values_after_params[values_after_params.length-1] !== values_before_params[n]){
                        rems.push('WARNING - arrtBB[' + i.toString() + '] (' + arrtBB[i][0] + ") : param[" + n + "] = "+ values_after_params[values_after_params.length-1]);
                    }
                }    
                arrtBB[i].values_after_params = values_after_params;  // firsts values ONLY (if exist) will be aplicated              
            }
        }
    }

    // try to correct arboBBC_crossing : modify arrtBB and N
    function try_to_correct_crossing_and_orphan(BBC_Def, closingNbTags) {
        var tmp_arboBBC_opening_orphan = [];
        var tmp_arboBBC_closing_orphan = [];
        var tmp_arboBBC_crossing = [];
        var tmp_arboBBC = [];
        var tmp_N = [];
        var tmp_arrt1, tmp_arrt2;
        var allOK = true;
        var lng1;
        var k;
        var before_node;
        var new_input;
        var new_node_BBC;
        var node_before;
        var corr_node_before;
        var node_after;
        var corr_node_after;

        function tmp_saves(){
            var lng, i;
            // make a copy of arboBBC_opening_orphan
            tmp_arboBBC_opening_orphan = [];
            lng = arboBBC_opening_orphan.length;
            for (i=0; i < lng; i++ ) tmp_arboBBC_opening_orphan.push(arboBBC_opening_orphan[i]);
            // make a copy of arboBBC_closing_orphan
            tmp_arboBBC_closing_orphan = [];
            lng = arboBBC_closing_orphan.length;
            for (i=0; i < lng; i++ ) tmp_arboBBC_closing_orphan.push(arboBBC_closing_orphan[i]);
            // make a copy of arboBBC_crossing
            tmp_arboBBC_crossing = [];
            lng = arboBBC_crossing.length;
            for (i=0; i < lng; i++ ) tmp_arboBBC_crossing.push(arboBBC_crossing[i]);
            // make a copy of arboBBC
            tmp_arboBBC = [];
            lng = arboBBC.length;
            for (i=0; i < lng; i++ ) tmp_arboBBC.push(arboBBC[i]);
            // make a copy of N
            tmp_N = [];
            lng = N.length;
            for (i=0; i < lng; i++ ) tmp_N.push(N[i]);
        }

        function tmp_restores(){
            var lng, i;
            // restore arboBBC_opening_orphan
            arboBBC_opening_orphan = [];
            lng = tmp_arboBBC_opening_orphan.length;
            for (i=0; i < lng; i++ ) arboBBC_opening_orphan.push(tmp_arboBBC_opening_orphan[i]);
            // restore arboBBC_closing_orphan
            arboBBC_closing_orphan = [];
            lng = tmp_arboBBC_closing_orphan.length;
            for (i=0; i < lng; i++ ) arboBBC_closing_orphan.push(tmp_arboBBC_closing_orphan[i]);
            // restore arboBBC_crossing
            arboBBC_crossing = [];
            lng = tmp_arboBBC_crossing.length;
            for (i=0; i < lng; i++ ) arboBBC_crossing.push(tmp_arboBBC_crossing[i]);
            // restore arboBBC
            arboBBC = [];
            lng = tmp_arboBBC.length;
            for (i=0; i < lng; i++ ) arboBBC.push(tmp_arboBBC[i]);
            // restore N
            N = [];
            lng = tmp_N.length;
            for (i=0; i < lng; i++ ) N.push(tmp_N[i]);
        }

        function insert_arrtBB_before(before_node, canonicOpeningLength){
            var tmp_arrt, z;
            arrtBB.push(arrtBB[0]); 
            for (z = arrtBB.length-1; z > before_node; z -= 1){
                tmp_arrt = arrtBB[z-1]; 
                if (tmp_arrt.perm) { 
                    if (tmp_arrt.perm >= before_node) tmp_arrt.perm++;
                }    
                tmp_arrt.index += canonicOpeningLength;
                arrtBB[z] = tmp_arrt;  
            }     
        }

        function delete_arrtBB_this(thisnode, canonicClosingLength){
            var tmp_arrt, z;
            for (z = thisnode; z < arrtBB.length-1; z += 1){
                tmp_arrt = arrtBB[z+1]; 
                if (tmp_arrt.perm) { 
                    if (tmp_arrt.perm >= before_node) tmp_arrt.perm--;
                }    
                tmp_arrt.index -= canonicClosingLength;
                arrtBB[z] = tmp_arrt;  
            }     
            arrtBB.pop();
        }

        function insert_N_before(before_node){
            var tmp__N, tmp__Np1, z;
            N.push(null);
            N.push(null);
            for (z = (N.length-1) / 2; z > before_node; z -= 1){
                tmp__N = N[2*(z-1) - 1]; 
                tmp__Np1 = N[2*(z - 1)];
                N[(2*z)-1] = tmp__N;
                N[2*z] = tmp__Np1;
            }     
        }

        function delete_N_this(thisnode){
            var tmp__N, tmp__Np1, z;
            for (z = thisnode; z < (N.length-1) / 2;  z += 1){
                tmp__N = N[(2*(z+1)) + 1]; 
                tmp__Np1 = N[2*(z +2)];
                N[(2*z)+1] = tmp__N;
                N[2*(z+1)] = tmp__Np1;
            }   
            N.pop();
            N.pop();  
        }

        function arrayRotate(arr, reverse){
            if (reverse) {
                arr.unshift(arr.pop());
            } else {
                arr.push(arr.shift());
            }  
            return arr;
        } 

        function node_clone(indice){
            var resnode;
            resnode = JSON.parse(JSON.stringify(arrtBB[indice]));
            resnode.absorbed = arrtBB[indice].absorbed;
            resnode.index = arrtBB[indice].index;
            resnode.input = arrtBB[indice].input;
            resnode.values_after_params = arrtBB[indice].values_after_params;
            resnode.values_before_params = arrtBB[indice].values_before_params;
            if (arrtBB[indice].perm) {
                resnode.perm = arrtBB[indice].perm;
            }
            return resnode;
        }

        // save majors arrays before all : if troubles to remove all crossing pairs, we could restore this cobfig
        tmp_saves();
        last_crossing_ind = -1;
        // First : try to reduce (repair) all crossing pairs ! How ? by permutation ! Object : decrease the gap between indices of a crossing pair if it is possible
        // the count of "permutations" on the second part of a crossing pair depend on the count of the first element of this pair in opening_closing
        // We begin by the first pair to the last BUT it's more easy to pop() the last pair SO we reverse FIRST the array of Crossing pairs
        arboBBC_crossing.reverse();
        for (var i=arboBBC_crossing.length-1; i>-1; i -= 1) {
            var r=0;
            // make rotations on opening_orphan such as the last element correspond to the first of the pair
            while ((arboBBC_opening_orphan[arboBBC_opening_orphan.length-1] !== arboBBC_crossing[i][0]) && (r < arboBBC_opening_orphan.length)  && allOK) {
                arrayRotate(arboBBC_opening_orphan, true);
                r += 1;
            }
            if (r === arboBBC_opening_orphan.length){                   // we have make an entire rotation of arboBBC_opening_orphan (impossible but, by caution ?)
                allOK = false;
            } else {
                var z=0;                                                // count the number of permutations for the second element of this pair
                var tmp_value = arboBBC_opening_orphan[arboBBC_opening_orphan.length-1];
                k = arboBBC_crossing[arboBBC_crossing.length-1][1];     // k = second element of the 'last' pair (remember : after reverse, so the first pair !)
                while ((arboBBC_opening_orphan[arboBBC_opening_orphan.length-1] === tmp_value) && allOK) {
                    var token = N[2*k];
                    token = token.replace(/\n/g,'');                    // Verification token is actually empty or spaces
                    token = token.replace(/\r/g,'');                    // 
                    if (token === '') {
                        tmp_arrt1 = arrtBB[k];                          // OK : permmutation of arrtBB AND N[]
                        tmp_arrt2 = arrtBB[k-1];
                        arrtBB[k-1] = tmp_arrt1; 
                        arrtBB[k-1].perm = k + z;
                        arrtBB[k] = tmp_arrt2; 
                        arrtBB[k].perm = k-1;
                        arboBBC_opening_orphan.pop();
                        tmp_arrt1 = N[(2*k) + 1];
                        tmp_arrt2 = N[(2*k) - 1];
                        N[(2*k) + 1] = tmp_arrt2;
                        N[(2*k) - 1] = tmp_arrt1;
                        z += 1;                                         // count oif permutation => +1
                        k -= 1;
                        //arboBBC_crossing.pop();
                        //arrayRotate(arboBBC_crossing, false);                       // the first begin last
                    } else {
                        allOK = false;  
                        last_crossing_ind = k;  
                        rems.push("UNRECOVERABLE ERROR : It's impossible to permute " + arrtBB[k][0] + " with the antecedent BBnode (" + arrtBB[k-1][0] + "), it's not empty between them : " + token);
                    }
                }
                arboBBC_crossing.pop();
                r = 0;
                z = 0;
            }
        }
        if (allOK) {  // 
            creation_of_drawer_structure(BBC_Def, closingNbTags);
        }
        if (!allOK || arboBBC_crossing.length > 0){
            // BAD NEW !!  Retrieve all arrays
            tmp_restores();
            return false;
        } else {
            // new arrt to be added must not have parameters !
            lng1 = arboBBC_closing_orphan.length;
            for (k=0; k < lng1; k++){
                if (BBC_Def[arrtBB[arboBBC_closing_orphan[k]].input].tabParHC.length > 0) {
                    allOK = false;    
                }
            }
            if (!allOK){
                // BAD NEW !!  Retrieve all arrays
                tmp_restores();
                return false;                
            } else {
                // Continue : add forgotten opening tags
                // first, by caution, sort arboBBC_closing_orphan :
                arboBBC_closing_orphan.sort(function (a, b) {
                    return a - b;
                });
                for (k = 0; k < lng1; k += 1) {
                    node_before = arboBBC_closing_orphan[k] - 1;
                    corr_node_before = arboBBC[node_before][2];
                    if (corr_node_before <= node_before) {
                        before_node = arboBBC[arboBBC_closing_orphan[k]-1][2];
                        new_input = arrtBB[arboBBC_closing_orphan[k]].input;
                        new_node_BBC = BBC_Def[arrtBB[arboBBC_closing_orphan[k]].input];

                        // Gap then insertion in arrtBB :
                        insert_arrtBB_before(before_node, new_node_BBC.CanonicOpening.length);
                        insert_N_before(before_node+1);
                        N[(2*before_node)+1] = new_node_BBC.CanonicOpening;
                        N[2*(before_node +1)] = '';
                        //temporary save for arrtBB[before_node+1] because it points on arrtBB[before_node]
                        tmp_arrt1 = node_clone(before_node+1);
                        // break the link / relation between arrtBB[before_node] and arrtBB[before_node+1]
                        arrtBB[before_node+1] = tmp_arrt1;
                        arrtBB[before_node][0] = new_node_BBC.CanonicOpening;
                        arrtBB[before_node].input = new_input;
                        arrtBB[before_node].add = true;
                        //arrtBB[before_node].index = arrtBB[before_node+1].index - new_node_BBC.CanonicOpening.length;
                    } else {
                        if (N[2*arboBBC_closing_orphan[k]] !== ''){
                            before_node = arboBBC[arboBBC_closing_orphan[k]+1][2];
                            new_input = arrtBB[arboBBC_closing_orphan[k]].input;
                            new_node_BBC = BBC_Def[arrtBB[arboBBC_closing_orphan[k]].input];

                            // Gap then insertion in arrtBB :
                            insert_arrtBB_before(before_node, new_node_BBC.CanonicOpening.length);
                            insert_N_before(before_node+1);
                            N[(2*before_node)+1] = new_node_BBC.CanonicOpening;
                            N[2*(before_node +1)] = '';
                            //temporary save for arrtBB[before_node+1] because it points on arrtBB[before_node]
                            tmp_arrt1 = node_clone(before_node+1);
                            // break the link / relation between arrtBB[before_node] and arrtBB[before_node+1]
                            arrtBB[before_node] = tmp_arrt1;
                            arrtBB[before_node+1][0] = new_node_BBC.CanonicOpening;
                            arrtBB[before_node+1].input = new_input;
                            arrtBB[before_node+1].add = true;
                            //arrtBB[before_node+1].index = arrtBB[before_node+2].index - new_node_BBC.CanonicOpening.length;
                        } else {          // delete this node !
                            rems.push('arrtBB[' + arboBBC_closing_orphan[k] + '] (' + arrtBB[arboBBC_closing_orphan[k]][0] + ') is deleted !');
                            delete_arrtBB_this(arboBBC_closing_orphan[k], BBC_Def[arrtBB[arboBBC_closing_orphan[k]].input].CanonicClosing.length);
                            delete_N_this(arboBBC_closing_orphan[k]);
                        }
                    }
                }
                if (arboBBC_closing_orphan.length > 0){
                    creation_of_drawer_structure(BBC_Def, closingNbTags);
                }
                // Continue : add forgotten closing tags
                // first, by caution, sort arboBBC_opening_orphan BUT important : reduce arboBBC_opening_orphan !
                // arboBBC_closing_orphan could not be reduced (before crossing) cause number of same closing_orphan was used in correcting crossing pair
                tmp_N = [];
                lng1 = arboBBC_opening_orphan.length;
                for (i = 0; i < lng1; i += 1) {
                    if (!inArray(arboBBC_opening_orphan[i], tmp_N)){
                        tmp_N.push(arboBBC_opening_orphan[i]);
                    }
                }
                arboBBC_opening_orphan.length = 0;
                lng1 = tmp_N.length;
                for (i = 0; i < lng1; i += 1) {
                    arboBBC_opening_orphan.push(tmp_N[i]);    
                }

                arboBBC_opening_orphan.sort(function (a, b) {
                    return a - b;
                });
                lng1 = arboBBC_opening_orphan.length;
                for (k = 0; k < lng1; k += 1) {
                    node_after = arboBBC_opening_orphan[k] + 1;
                    corr_node_after = arboBBC[node_after][2];
                    if (corr_node_after >= node_after) {
                        before_node = arboBBC[arboBBC_opening_orphan[k]+1][2]+1;
                        new_input = arrtBB[arboBBC_opening_orphan[k]].input;
                        new_node_BBC = BBC_Def[arrtBB[arboBBC_opening_orphan[k]].input];

                        // Gap then insertion in arrtBB :
                        insert_arrtBB_before(before_node, new_node_BBC.CanonicClosing.length);
                        insert_N_before(before_node+1);
                        N[(2*before_node) + 1] = new_node_BBC.CanonicClosing;
                        N[2*(before_node +1)] = '';
                        //temporary save for arrtBB[before_node+1] because it points on arrtBB[before_node]
                        tmp_arrt1 = node_clone(before_node+1);
                        arrtBB[before_node][0] = new_node_BBC.CanonicClosing;
                        arrtBB[before_node].add = true; 
                        arrtBB[before_node].input = new_input;
                        // break the link / relation between arrtBB[before_node] and arrtBB[before_node+1]
                        arrtBB[before_node+1] = tmp_arrt1;                      
                    } else {
                        if (N[(2*arboBBC_opening_orphan[k])+2] !== '') {
                            before_node = arboBBC[arboBBC_opening_orphan[k]-1][2];
                            new_input = arrtBB[arboBBC_opening_orphan[k]].input;
                            new_node_BBC = BBC_Def[arrtBB[arboBBC_opening_orphan[k]].input];

                            // Gap then insertion in arrtBB :
                            insert_arrtBB_before(before_node, new_node_BBC.CanonicClosing.length);
                            insert_N_before(before_node);
                            N[(2*before_node) + 1] = new_node_BBC.CanonicClosing;
                            N[2*(before_node +1)] = '';
                            //temporary save for arrtBB[before_node+1] because it points on arrtBB[before_node]
                            tmp_arrt1 = node_clone(before_node+1);
                            arrtBB[before_node][0] = new_node_BBC.CanonicClosing;
                            arrtBB[before_node].input = new_input;
                            arrtBB[before_node].add = true;
                            //arrtBB[before_node].index = arrtBB[before_node+1].index - new_node_BBC.CanonicOpening.length;
                            // break the link / relation between arrtBB[before_node] and arrtBB[before_node+1]
                            arrtBB[before_node+1] = tmp_arrt1;
                        } else {          // delete this node !
                            rems.push('arrtBB[' + arboBBC_opening_orphan[k] + '] (' + arrtBB[arboBBC_opening_orphan[k]][0] + ') is deleted !');
                            delete_arrtBB_this(arboBBC_opening_orphan[k], BBC_Def[arrtBB[arboBBC_opening_orphan[k]].input].CanonicOpening.length);
                            delete_N_this(arboBBC_opening_orphan[k]);
                        }
                    }
                }
                if (arboBBC_opening_orphan.length > 0){
                    creation_of_drawer_structure(BBC_Def, closingNbTags);
                }
                analyse_arbo();
                return true;
            }
        }
    }

    // in arboBBC some laws must be observed : 1°) each node have a corespondent node 2°) no crossing of correspondent nodes  <==> all daughters between 2 correspondents nodes / tags
    function analyse_arbo(){
        var Verif = [];
        var k, lng;
        stats_maxchain = [];
        lng = arboBBC.length;
        for (i = 0; i < lng; i += 1){                // another orphan ???
            if ((arboBBC[i][2] == -1) && (!arrtBB[i].absorbed)) {
                if (arrtBB[i][0].substr(1, 1) == '/') {
                    arboBBC_closing_orphan.push(i);            
                } else {
                    arboBBC_opening_orphan.push(i);                      
                }
            }
            if (arboBBC[i][3].length > stats_maxchain.length){
                stats_maxchain.length = 0;
                for (k=0; k<arboBBC[i][3].length; k++) {
                    stats_maxchain.push(arboBBC[i][3][k]);    
                }    
            }
        }
        for (i = 0; i < lng; i +=1) Verif.push(false);
        for (i = 0; i < lng; i +=1) {
            if (Verif[i] === false) {
                if (arboBBC[i][2] !== -1) k=arboBBC[i][2];
                if (k >= i){                                  // = because autoclosing !
                    var good = true;
                    for (var p=0; p<arboBBC[i][1].length; p++){
                        good = good && (i < arboBBC[i][1][p]) && (k > arboBBC[i][1][p]);                
                    }
                    if (good) {
                        Verif[i]=true;
                        Verif[k]=true;
                    }
                }
            }
        }   
        for (i=0; i< lng; i++){
            if (!Verif[i] && (!arrtBB[i].absorbed)) {
                rems.push('VERIF - arboBBC[' + i.toString() + '] is not good !');
            }
        }  
    }

    // create textBB_after (text_in after corrections) and 
    // textBB_after_BB to "see" corrections
    function create_textBB_after(BBC_Def){
        textBB_after = '';  
        textBB_after_BB = '';
        var text = '';
        var F = [];
        var lng1, lng2;

        textBB_after_BB +=  N[0];  
        F.push(N[0]);
        lng1 = arrtBB.length;
        for (i = 0; i < lng1; i += 1) {
            if (arrtBB[i].add !== undefined) {
                F.push(arrtBB[i][0]);
                F.push('');   
                textBB_after_BB += '<b><span style=" color:#f92672">' + arrtBB[i][0] + '</span></b>';
            } else {
                if (arrtBB[i].absorbed){
                    F[F.length-1] +=  N[(2*i)+1] + N[2*(i+1)];
                    textBB_after_BB += N[(2*i)+1] + N[2*(i+1)];  
                } else {                                                  // neigher ADD nor ABSORBED
                    text = arrtBB[i][0];   
                    F.push(arrtBB[i][0]);
                    F.push(N[2*(i+1)]); 
                    if (arrtBB[i].oldc !== undefined){                    // closing
                        text = text.replace('/', '<u><b>/</b></u>');
                    }
                    if (arrtBB[i].old !== undefined){
                        text = '<i>' + text + '</i>';
                    }                                                     // opening
                    if (arrtBB[i].values_after_params !== undefined) {
                        lng2 = arrtBB[i].values_after_params.length;
                        for (var k=0; k < lng2; k++){
                            if (arrtBB[i].values_after_params[k] != arrtBB[i].values_before_params[k]) {
                                text = text.replace(arrtBB[i].values_before_params[k], '<b><u>' + arrtBB[i].values_after_params[k] + '</u></b>');
                            }
                        } 
                    }
                    if (arrtBB[i].perm !== undefined){
                        textBB_after_BB += '<span style=" color:#3060c1">' + text + '</span>' + N[2*(i+1)];
                    } else {
                        if (i === last_crossing_ind - 1) { 
                        //textBB_after_BB += '<span style=" color:#9a5f0b">' + text + '</span>' + N[2*(i+1)];
                            textBB_after_BB += '<span style=" color:#066602">' + text + '</span><b><span style=" color:#f92672">' + N[2*(i+1)] + '</span></b>';
                        } else {
                            textBB_after_BB += '<span style=" color:#066602">' + text + '</span>' + N[2*(i+1)];     
                        }
                    }
                }
            }
        } 
        textBB_after = F.join('');
        textBB_after_BB = textBB_after_BB.replace(/\n/g,"<br>");
    }

    // use trad to create output_trad_text
    function create_new_code(BBC_Def, N, afunctions){
        output_trad_text = ''; 
        var out = [];   
        var ready = [];
        var trad = '';
        var tconds;
        var lng1, lng2;
        var corr;
        var tparams;
        var trad_open, trad_close, newSplit, lRE, filter, p;

        for (i=0, lng1 = arrtBB.length; i < lng1; i++) ready.push(false);
        for (i=0, lng2 = N.length; i < lng2; i++) out.push(N[i]);
        for (i=0; i < lng1; i++)  {
            // is there a function ?
            if (BBC_Def[arrtBB[i].input].trad === 'function') {
                filter = BBC_Def[arrtBB[i].input].name + "_trad";                            
                var x=0;
                while (filter !== namefunctions[x]) x += 1;
                trad = afunctions[x](out[(2*(i+1))]);
            } else {
                trad = BBC_Def[arrtBB[i].input].trad;    
            }
            corr = arboBBC[i][2];
            if (!ready[i]){
                if (!arrtBB[i].absorbed){
                    // replace values of parameters in trad
                    // first : conditions ?
                    tconds = trad.match(REcondCap);
                    if (tconds !== null){
                        for (var c=0; c<tconds.length; c += 1){
                            tparams = 0;
                            for (p = 0; p<BBC_Def[arrtBB[i].input].params.length; p += 1) {
                                lRE = new RegExp ('\\'+BBC_Def[arrtBB[i].input].params[p], 'g');
                                if (lRE.test(tconds[c]) && (arrtBB[i].values_after_params[p] !== null)) tparams += 1;
                            }
                            if (tparams === 0){                           // condition without parameters !! ???
                                trad = trad.replace(tconds[c], '');
                            } 
                        }
                    }
                    trad = trad.replace(/\{/g, '').replace(/\}/g, '');
                    if (BBC_Def[arrtBB[i].input].params){
                        for (p=0; p<BBC_Def[arrtBB[i].input].params.length; p += 1) {
                            lRE = new RegExp ('\\'+BBC_Def[arrtBB[i].input].params[p], 'g');
                            if (BBC_Def[arrtBB[i].input].params[p] !== null){
                                trad = trad.replace(lRE, arrtBB[i].values_after_params[p]);
                            }
                        }
                    }
                    var F_split = trad.split('$E');
                    if (F_split.length > 2){                           // must be tested because function trad !!
                        trad_open = trad.substr(0,1);
                        trad_close = trad.substr(-1);
                        newSplit = trad_close + '$E' + trad_open;
                        F_split = trad.split(newSplit);
                        if (F_split.length > 2){
                            console.log("ERROR : " + arrtBB[i][0] + ' trad cannot have more than one ' + newSplit + ' : [' + trad + ']');   
                            rems.push("ERROR : " + arrtBB[i][0] + ' trad cannot have more than one ' + newSplit + ' : [' + trad + ']');   
                        } else {
                            F_split[0] = F_split[0].replace(REparext, N[2*(i+1)]);
                            if (F_split.length>1) F_split[1] = F_split[1].replace(REparext, N[2*(i+1)]);
                            out[(2*i)+1] = F_split[0] + trad_close;
                            ready[i] = true;
                            if (corr !== i){
                                out[(2*corr)+1] =  trad_open + F_split[1];
                                ready[corr] = true;
                            }                                
                        }
                    } else {
                        out[(2*i)+1] = F_split[0];
                        ready[i] = true;
                        if (corr !== i){
                            out[(2*corr)+1] =  F_split[1];
                            ready[corr] = true;
                        }
                    }
                } else {   // absorbed
                    out[(2*i)+1] = N[(2*i)+1];
                    out[2*(i+1)] = N[2*(i+1)];
                }
            }        
        }    
        output_trad_text = out.join('');
    }

    // replace smileys in output_trad_text 
    function parse_output_with_smileys(cod2smil){
        var cod, lng, smiley, REcod, tmp;

        // var Metas = ['!','^','$','(',')','[',']','{','}','?','+','*','.','/','\\','|'];  // metacharacters in RegExp
        var OrdMetas = [33,94,36,40,41,91,93,123,125,63,43,42,46,47,92,124];

        for (cod in cod2smil){
            if (cod2smil.hasOwnProperty(cod)) {
                tmp='';
                for (t=0, lng = cod.length; t < lng; t += 1){
                    if (inArray(cod.charCodeAt(t), OrdMetas)){
                        tmp += String.fromCharCode(92)+cod.substr(t,1);
                    } else {
                        tmp += cod.substr(t,1);
                    }
                }
                REcod = new RegExp (tmp, 'g');
                smiley = '<img src="./smileys/' + cod2smil[cod] + '" alt="">';
                output_trad_text = output_trad_text.replace(REcod, smiley);
            }
        }
    }

    var result = {};

    function parseBBcode(BBC_Def, text_in, cod2smil, afunctions) {
        // extract all BBnodes from text_in and save thme in arrtBB
        // first improvement : arrtBBsensitive (case sensitive) and arrtBBanticlosing ('\' in replacement of '/')
        parse_and_create_arrtBB(BBC_Def, text_in);
        arrtBB.sort(function (a, b) {
            return a.index - b.index;
        });
        // create array N : textnode / BBnode / textnode / BBnode / ... / BBnode / textnode
        create_N_arrt(text_in);
        // second improvement : cleaning tags with Canonics forms (opening and closing)
        cleaning_of_arrtBB(BBC_Def);
        // create arboBB
        creation_of_drawer_structure(BBC_Def, closingNbTags);
        // verification and use of filter for parameters
        correct_parameters(BBC_Def, afunctions);

        analyse_arbo();

        // try to correct crossing BBNodes and orphans BBNodes
        if (try_to_correct_crossing_and_orphan(BBC_Def, closingNbTags)) {
            //rems.length = 0;    
            rems.push('---- corrections of crossing and orphan realized ----');

            correct_parameters(BBC_Def, afunctions);
            //create_textBB_after && textBB_after_BB
            create_textBB_after(BBC_Def, afunctions);
            //create_output_trad_text                            // New N !
            create_new_code(BBC_Def, N, afunctions);
            // parse smileys in create_output_trad_text
            parse_output_with_smileys(cod2smil);
            output_trad_text = output_trad_text.replace(/\n/g, '<br>');
            rems.push('OK');
        } else {
            rems.push('Non OK');
            //create_textBB_after && textBB_after_BB
            create_textBB_after(BBC_Def, afunctions);
            output_trad_text = '';
        }    

        result.rems = rems;
        result.arrtBB = arrtBB;
        result.arrtBBsensitive = arrtBBsensitive;
        result.arrtBBanticlosing = arrtBBanticlosing;
        result.arboBBC = arboBBC;
        result.arboBBC_opening_orphan = arboBBC_opening_orphan;
        result.arboBBC_closing_orphan = arboBBC_closing_orphan;
        result.arboBBC_crossing = arboBBC_crossing;
        result.textBB_after = textBB_after;
        result.textBB_after_BB = textBB_after_BB;
        result.output_trad_text = output_trad_text;

        return result;
    }

    return {
    // function init - input : 
    //      struct : an array of object to define each of "mark" (BBCode / HTML balise / etc ...),
    //      afunctions : an array of functions (by default null);
    //      rems_before_corrections
        init: function (BBC_Def, afunctions) {
            var ret;
            ret = initiate(BBC_Def, afunctions);
            return ret;
        },
    // function parse 
        parse: function (BBC_Def, text_in, cod2smil, afunctions) {
            var ret;
            ret = parseBBcode(BBC_Def, text_in, cod2smil, afunctions);
            return ret;
        }
    };

})();

if (typeof module !== 'undefined' && module.exports) {
    module.exports = MarkValser;
} else {
    if ((typeof define === 'function') && define.amd) {
        define('MarkValser', [], function() {
            return MarkValser;
        });
    }
}
