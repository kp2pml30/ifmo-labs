1.     ������� �� ���������� ��

1.S. Students

���-������ �� ������� �������������� �������: create index StudentGroupToId on Students using hash (GroupId); create unique index StudentsGidToSid on Students using btree (GroupId, StudentId);
���-������ �� ������� �������������� �������: create unique index StudentIdAndGroupToRecord on Students using hash (StudentId, GroupId); create unique index StudentsGidToSid on Students using btree (GroupId, StudentId);
������������� ��� ����������� ������: create unique index StudentIdAndGroupToRecord on Students using hash (StudentId, GroupId);
������ ����/����������: ��-5.6.1 ��� create index StudentNameIdx on Students using btree (StudentName);
������ ����/����������: ��-5.5.1 ��� create index StudentGroupToId on Students using hash (GroupId);
������ ����/����������: ��-5.5.2 ��� create index StudentGroupToId on Students using hash (GroupId);
������ ����/����������: ��-5.5.3 ��� create index StudentGroupToId on Students using hash (GroupId);
������ ����/����������: ��-6.5.1 ��� create unique index StudentsGidToSid on Students using btree (GroupId, StudentId);

1.G. Groups

1.C. Courses

������ ����/����������: ��-5.5.1 ��� create unique index CoursesIdUniq on Courses using hash (CourseId);
������ ����/����������: ��-5.5.2 ��� create unique index CoursesIdUniq on Courses using hash (CourseId);
������ ����/����������: ��-5.5.3 ��� create unique index CoursesIdUniq on Courses using hash (CourseId);

1.L. Lecturers

1.P. Plan

�� unique ������ (� ������): create index GiCiExistsInPlan on Plan using hash (GroupId, CourseId);
������ ����/����������: ��-6.3.2 ��� create index GiCiExistsInPlan on Plan using hash (GroupId, CourseId);
������ ����/����������: ��-6.4.1 ��� create index GiCiExistsInPlan on Plan using hash (GroupId, CourseId);
������ ����/����������: ��-6.4.2 ��� create index GiCiExistsInPlan on Plan using hash (GroupId, CourseId);

1.M. Marks

���-������ �� ������� �������������� �������: create index MarkByStudentIdExists on Marks using hash (StudentId); create index SiCiInMarks on Marks using btree (StudentId, CourseId, Mark);
���-������ �� ������� �������������� �������: create index MarkByStudentIdExists on Marks using hash (StudentId); create index SiAndMark on Marks using btree (StudentId, Mark);
�� unique ������ (� ������): create index SiCiInMarks on Marks using btree (StudentId, CourseId, Mark);
��� ������� �� PK: create unique index on Marks using hash (StudentId, CourseId);
�������� ����������� ������ ������: create index MarkCourseToStudent on Marks using hash (CourseId, Mark);
������ ����/����������: ��-5.3.1 ��� create index MarkCourseToStudent on Marks using hash (CourseId, Mark);

2.     ������� ����

2.Q. ������

2.I. �������

�� ������� �������: create index on Groups using hash (GroupName);
�� ������� �������: create index on Courses using btree (CourseName, CourseId);

3.     ����� �������

3.1.Q. ������

3.1.I. �������

���������� ������� �� ��������

3.2.Q. ������

3.2.I. �������

3.3.Q. ������

3.3.I. �������