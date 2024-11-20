abstract sig User {}

var abstract sig Report {
    var about: one Internship,
}

sig Student extends User {
	studiesAt: one University,
    var appliesFor: set Internship,
    var particiaptesIn: set Internship,
    var fills: set Form,
    var writes: set Report,
}

sig Company extends User {
    var creates: set Internship,
    var archives: set PastProject,
    var writes: set Report,
}

sig University extends User {
    var supervises: set Student,
    var reads: set Complaint,
}

sig Internship {
    var status: Status
}

var sig PastProject {}

var sig Complaint extends Report {}

var sig Feedback extends Report {}

var sig Form {
    var _for_: Internship,
}

enum Status { Open, Screening, Ongoing, Finished }

// Facts
// ----------------------------------------------------------------------
// Old facts
// ----------------------------------------------------------------------

// All internships must have exactly one company that offers them
fact OneOfferingCompany {
    always all i: Internship |
    one c: Company | i in c.creates
}

// All students must study at exactly one university and that university
// must supervise them
fact EveryStudentBelongsToUniversity {
    always all s: Student | 
    one u: University | (s.studiesAt = u) and (s in u.supervises)
}

// All univesities can only read complaints that are made for internships
// involving their students
fact UniversityReadsRelevantComplaints {
    always all u: University, c: Complaint |
    (c in u.reads) implies (c.about in u.supervises.particiaptesIn)
}

// Each student can only fill forms for internships that they have applied
// for
fact StudentFillsFormsForAppliedInternships {
    always all s: Student, f: Form |
    (f in s.fills) implies (f._for_ in s.appliesFor)
}

// Each student can submit only one form per internship
fact UniqueFormPerStudentPerInternship {
    always all s: Student, i: Internship |
    lone f: Form | (f in s.fills) and (f._for_ = i)
}

// Each form must be filled by a single student
fact FormFilledBySingleStudent {
    always all f: Form |
    one s: Student | f in s.fills
}

// Each student can only participate in internships for which they have
// applied for and filled a form
fact StudentParticipatesInAppliedInternships {
    always all s: Student, i: Internship |
    i in s.particiaptesIn implies once ((i in s.appliesFor) and
    (one f: Form | f._for_ = i and f in s.fills))
}

// Each past project is associated with a company that has offered it
fact PastProjectHasOfferingCompany {
    always all p: PastProject |
    one c: Company | p in c.archives
}

// A report can only be written by a single student or a single company
// involved in the internship and cannot have more than one author
fact UniqueReportAuthor {
    always all r: Report |
    (one s: Student | r in s.writes and no c: Company | r in c.writes) or
        (one c: Company | r in c.writes and no s: Student | r in s.writes)
}

// A report can only be written by a student participating in the internship
fact ReportWrittenByParticipatingStudent {
    always all r: Report, s: Student |
    r in s.writes implies (r.about in s.particiaptesIn)
}

// A company can only write reports for an internship it has created and
// in which at least one student participates
fact ReportWrittenByOfferingCompany {
    always all r: Report, c: Company |
    r in c.writes implies (r.about in c.creates and 
    some s: Student | r.about in s.particiaptesIn)
}

// A complaint can only be made if there is another party involved in the
// internship
fact ComplaintMadeForActiveInternship {
    always all c: Complaint |
    some s: Student | c.about in s.particiaptesIn
}

// Each student or company can only write one feedback for each internship
// they are involved in
fact UniqueFeedbackPerInternship {
    always all s: Student, c: Company, i: Internship |
    lone f: Feedback | (f in s.writes or f in c.writes) and f.about = i
}

// ----------------------------------------------------------------------
// New facts
// ----------------------------------------------------------------------

// A student can only apply for internships that are open or in screening
fact StudentAppliesForOpenInternships {
    always all s: Student, i: Internship |
    i in s.appliesFor implies (i.status = Open or i.status = Screening)
}

// A student must continue to apply for an internship until it is ongoing
fact StudentApplicationUntilOngoing {
    always all s: Student, i: Internship |
    i.status = Open and i in s.appliesFor and (i.status' = Open or
    i.status' = Screening) implies i in s.appliesFor'
}

// A student can only participate in internships that are ongoing or finished
fact StudentParticipatesInOngoingInternships {
    always all s: Student, i: Internship |
    i in s.particiaptesIn implies (i.status = Ongoing or i.status = Finished)
}

// All ongoing internships must have at least one student participating in them
fact OngoingInternshipsHaveParticipants {
    always all i: Internship |
    i.status = Ongoing implies some s: Student | i in s.particiaptesIn
}

// A student must continue to participate in an internship until it is finished
fact StudentParticipationUntilFinished {
    always all s: Student, i: Internship |
    i in s.particiaptesIn implies always i in s.particiaptesIn
}

// A complaint can only be made for internships that are ongoing
fact ComplaintMadeForOngoingInternship {
    always all c: Complaint |
    c.about.status = Ongoing
}

// A feedback can only be written for internships that are finished
fact FeedbackWrittenForFinishedInternship {
    always all f: Feedback |
    f.about.status = Finished
}

// A company can only remove an internship that is finished
fact CompanyCannotRemoveOngoingInternship {
    always all c: Company, i: Internship |
    i in c.creates and i.status != Finished implies i in c.creates'
}

// All internships will eventually be finished
fact AllInternshipsFinish {
    eventually all i: Internship |
    i.status = Finished
}

// The order of the statuses of an internship must be preserved
fact StatusOrder {
    always all i: Internship |
    (i.status = Open implies i.status' = Open or i.status' = Screening)
    and (i.status = Open implies eventually i.status = Screening)
    and (i.status = Screening implies i.status' = Screening or i.status' = Ongoing)
    and (i.status = Ongoing implies i.status' = Ongoing or i.status' = Finished)
    and (i.status = Ongoing implies eventually i.status = Finished)
    and (i.status = Finished implies i.status' = Finished)
}

// Predicates -------------------------------------------------------------
pred InitialSituation {
    # Student = 3
    # Company = 2
    # University = 2
    # Internship = 3
    # PastProject = 0
    all i: Internship |
    i.status = Open
}

pred InternshipEvolution {
    eventually all i: Internship | i.status = Open implies i.status' = Screening
    eventually all i: Internship | i.status = Screening implies i.status' = Ongoing
    eventually all i: Internship | i.status = Ongoing implies i.status' = Finished
}

pred InternshipApplication {
    eventually all s: Student, i: Internship |
    i.status = Open implies after i in s.appliesFor and i.status = Screening
}

pred InternshipConclusion {
    eventually all i: Internship, c: Company |
    i.status = Finished and i in c.creates implies after no s: Student | i in s.particiaptesIn
    and #c.archives' = #c.archives + 1
}

pred show {
    InternshipEvolution;InternshipApplication;
    InternshipConclusion;InitialSituation
}
run show for 7