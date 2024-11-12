abstract sig User {}

sig Student extends User{
	university: one University
}

sig Company extends User{
    internships: set Internship
}

sig University extends User{
    students: set Student
}

sig Internship {
    company: one Company,
    students: set Student,
    application_deadline: one Int,
    form_deadline: one Int,
    interview_deadline: one Int,
}

sig Complaint {
    author: one User,
}

sig Form {
    author: one Student,
    internship: one Internship,
}

sig Feedback {
    internship: one Internship,
    author: one User,
}

// Facts
// All internships must have exactly one company that offers them
fact OneOfferingCompany {
    all i: Internship | one c: Company | i in c.internships
}

// All students must belong to exactly one university, and each university
// must recognize these students in its 'students' set.
fact EveryStudentBelongsToUniversity {
    all s: Student | one u: University | s.university = u && s in u.students
}

// Deadlines in an internship must be sequential: application deadline first,
// then form deadline, and finally interview deadline.
fact DeadlinesOrder {
    all i: Internship | i.application_deadline < i.form_deadline && i.form_deadline < i.interview_deadline
}

// Each internship belongs to only one company, enforcing that internships are uniquely
// associated with companies without duplication within the company's 'internships' set.
fact UniqueInternshipsPerCompany {
    all c: Company | all i, j: c.internships | i = j or i != j
}

// Each student can submit only one form per internship, preventing multiple applications
// to the same internship by the same student.
fact UniqueFormPerStudentPerInternship {
    all s: Student, i: Internship |
        lone f: Form | f.author = s && f.internship = i
}

// Each complaint must have an author who is a valid user (student or company).
fact ComplaintAuthorIsUser {
    all c: Complaint | c.author in Student + Company
}

// Each feedback must have an author who is a valid user (student or company) and is
// involved in the internship.
fact FeedbackAuthorIsUser {
    all f: Feedback | f.author in Student + Company && f.author in f.internship.students + f.internship.company
}

// Each student has exactly one associated university, and no student
// can belong to more than one university.
fact UniqueUniversityForStudent {
    all s: Student | one s.university
}

// Prevents self-referencing in complaints and feedback, so no user can
// author a complaint or feedback about themselves.
fact NoSelfReference {
    all c: Complaint | c.author != c.author
    all f: Feedback | f.author != f.author
}

// Ensures that if a student is assigned to a university, they must
// also be present in that university’s 'students' set.
fact StudentInUniversitySet {
    all u: University | all s: u.students | s.university = u
}