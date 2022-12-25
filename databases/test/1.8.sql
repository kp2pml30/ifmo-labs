select distinct SessionId
from Sessions natural join Problems left join Runs using (SessionId, Letter)
group by SessionId
having count(*) = sum(Runs.Accepted)
